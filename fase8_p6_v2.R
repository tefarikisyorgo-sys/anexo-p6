# =====================================================================
# fase8_p6_v2.R  ·  Pregunta 6, versión 2 (13-nov-2026)
# ¿Qué 2-3 intervenciones de marketing/CRO priorizar para mover clientes hacia la compra, y en qué estado ubicarlas?
#
# La P6 se separa en dos partes:
#   A) DÓNDE intervenir (diagnóstico): se usa el método de Aung & Kumoi (2026, IEEE Access, sec. III-F y III-G)
#      sobre la misma cadena de P4 (orden 1, con autotransiciones, visitas cortadas en su 1ª compra).
#      - "sube" (el método del paper): la probabilidad i -> j sube 10% relativo (0,40 -> 0,44). Esa masa se descuenta,
#        en proporción, de las otras salidas de i hacia páginas (no se tocan la autotransición, Compra ni Abandono).
#        Se prueba UNA flecha a la vez, en todas las flechas entre páginas con probabilidad >= 2%.
#      - "baja" (extensión nuestra): la probabilidad i -> j baja 10% relativo y esa masa se reparte, en proporción,
#        en las otras salidas de i hacia páginas. Se usa para la flecha que más resta (Carrito -> Producto).
#      - "fuga" (extensión nuestra): igual que "baja", pero sobre i -> Abandono (la fuga de P5).
#      - Impacto: delta = l'(B' - B) (paper, ec. 5), en cambio relativo. Compradores: probabilidad de comprar en la
#        visita. No compradores (no compran en julio por definición): probabilidad de llegar al Checkout.
#      - El 10% es un empujón de referencia, igual para todas las flechas, para compararlas. No predice el efecto real.
#   B) QUÉ hacer: datos descriptivos para diseñar las acciones (qué significa cada flecha y qué pasa entre visitas).
#
# NO MODIFICA df_falabella_estados (trabaja sobre una copia: d).
# OBJETOS QUE CREA: d, h, TR, ST, TRs, STs, clientes, MB, barrido, fugas, elegidas, eleg_ic, alfa_sens, chequeo_auto,
#                   base_tab, robustez_pre, flechas, entre_visitas, tiempos (y funciones: filas, inicio, modificar,
#                   baja, llegar, efecto, ratio_ic).
# ARCHIVOS QUE GUARDA (carpeta "resultados_p6_v2", al lado de donde se corre el script):
#   p6v2_barrido.csv, p6v2_fugas.csv, p6v2_intervenciones.csv, p6v2_sensibilidad_alfa.csv, p6v2_chequeos.csv,
#   p6v2_robustez_pre.csv, p6v2_flechas.csv, p6v2_entre_visitas.csv, p6v2_anexo.json,
#   p6v2_fig_ubicacion.png/.svg, p6v2_fig_impacto.png/.svg, p6v2_fig_tiempo.png/.svg
# PAQUETES: data.table, jsonlite, ggplot2 (y svglite para los .svg). Tiempo aproximado: 4-6 minutos.
# =====================================================================
suppressMessages({library(data.table); library(jsonlite); library(ggplot2)})
set.seed(2026)
B <- 500
SALIDA <- "resultados_p6_v2"; dir.create(SALIDA, showWarnings = FALSE)
RDS <- if (file.exists("df_falabella_estados.rds")) "df_falabella_estados.rds" else
  "/mnt/user-data/uploads/Script R tesis/df_falabella_estados.rds"
TRANS <- c("PORTADA","BUSQUEDA","LISTADO","PRODUCTO","AGREGAR_CARRO","CARRITO","CHECKOUT","CUENTA_SERVICIOS","OTROS")
NOMBRE <- c(PORTADA="Portada", BUSQUEDA="Búsqueda", LISTADO="Listado", PRODUCTO="Producto", AGREGAR_CARRO="Agregar al carro",
            CARRITO="Carrito", CHECKOUT="Checkout", CUENTA_SERVICIOS="Cuenta y servicios", OTROS="Otros", ABANDONO="Abandono", COMPRA="Compra")
ABS <- c("COMPRA", "ABANDONO")

# ---------------------------------------------------------------- datos (misma cadena de P4)
d <- as.data.table(readRDS(RDS))
sel <- d$node_type_agrupacion == "SLP_RESIDUAL" & tolower(trimws(d$page_name)) == "warrantyselection"
d[sel, estado := "AGREGAR_CARRO"]                                   # garantía = Agregar al carro (decisión de P4)
h <- d[, .(uid = unified_id, visit_id, seg = cliente_compro_en_ventana, dia = as.Date(date_time_start), node_order,
           t = date_time_start, estado, product_id)]
setorder(h, visit_id, dia, node_order, t); h[, pos := seq_len(.N), by = visit_id]
h[, pc := if (any(estado == "COMPRA")) min(pos[estado == "COMPRA"]) else NA_integer_, by = visit_id]
h <- h[is.na(pc) | pos <= pc]; h[, g := fifelse(seg == 1, "C", "NC")]
h[, `:=`(prev = shift(estado, 1L, fill = "INICIO"), nxt = shift(estado, -1L, fill = "ABANDONO")), by = visit_id]
TR <- h[estado != "COMPRA", .N, by = .(g, uid, prev, cur = estado, nxt)]
ST <- h[pos == 1L, .N, by = .(g, uid, first = estado)]
hs <- h[, .(g, uid, visit_id, estado)][, keep := estado != shift(estado, fill = ""), by = visit_id][keep == TRUE]
hs[, `:=`(prev = shift(estado, 1L, fill = "INICIO"), nxt = shift(estado, -1L, fill = "ABANDONO")), by = visit_id]
TRs <- hs[estado != "COMPRA", .N, by = .(g, uid, prev, cur = estado, nxt)]
STs <- hs[, .SD[1], by = visit_id][, .N, by = .(g, uid, first = estado)]

# ---------------------------------------------------------------- funciones
filas <- function(tr) { x <- tr[, .(N = sum(N)), by = .(key = cur, cur, nxt)]; x[, p := N / sum(N), by = key][] }
inicio <- function(st) { x <- st[, .(N = sum(N)), by = first]; x[, key := first]; x[, p := N / sum(N)][] }
modificar <- function(F, i, j, alfa = 0.10, tipo = "sube") {   # sube (paper) / fuga (extensión: i -> Abandono baja)
  F <- copy(F); F[, mod := cur == i]; obj <- if (tipo == "sube") j else "ABANDONO"
  F[mod == TRUE, elig := !(nxt %in% c(ABS, i, obj))]
  F[mod == TRUE, `:=`(masa = alfa * sum(p[nxt == obj]), base = sum(p[elig])), by = key]
  F[mod == TRUE & nxt == obj & base > 0, p := p * (1 + if (tipo == "sube") alfa else -alfa)]
  sg <- if (tipo == "sube") -1 else 1
  F[mod == TRUE & elig == TRUE & base > 0, p := p + sg * masa * p / base]
  F[, c("mod", "elig", "masa", "base") := NULL][] }
baja <- function(F, i, j, alfa = 0.10) {                          # extensión: i -> j (página) baja
  F <- copy(F); F[, mod := cur == i]; F[mod == TRUE, elig := !(nxt %in% c(ABS, i, j))]
  F[mod == TRUE, `:=`(masa = alfa * sum(p[nxt == j]), base = sum(p[elig])), by = key]
  F[mod == TRUE & nxt == j & base > 0, p := p * (1 - alfa)]
  F[mod == TRUE & elig == TRUE & base > 0, p := p + masa * p / base]
  F[, c("mod", "elig", "masa", "base") := NULL][] }
llegar <- function(F, L, meta) {                                  # probabilidad de llegar a 'meta' desde la entrada
  fin <- c(ABS, meta); F <- F[!(cur %in% meta)]; F[, dest := nxt]
  S <- unique(F$key)
  Q <- matrix(0, length(S), length(S), dimnames = list(S, S)); R <- matrix(0, length(S), length(fin), dimnames = list(S, fin))
  q <- F[dest %in% S]; r <- F[dest %in% fin]
  Q[cbind(match(q$key, S), match(q$dest, S))] <- q$p
  r <- r[, .(p = sum(p)), by = .(key, dest)]; R[cbind(match(r$key, S), match(r$dest, fin))] <- r$p
  Bm <- solve(diag(length(S)) - Q, R)                              # B = (I - Q)^-1 R
  L <- copy(L); L[, dest := key]; lt <- L[dest %in% S]; la <- L[dest %in% fin]
  out <- colSums(Bm[lt$dest, , drop = FALSE] * lt$p); out[la$dest] <- out[la$dest] + la$p
  sum(out[if (length(meta)) meta else "COMPRA"]) }
META <- list(C = character(0), NC = "CHECKOUT")
cambiar <- function(F, e, alfa = 0.10) if (e$tipo == "baja") baja(F, e$i, e$j, alfa) else modificar(F, e$i, e$j, alfa, e$tipo)

# ---------------------------------------------------------------- A) barrido de flechas (orden 1)
barrido <- list(); fugas <- list()
for (gg in c("C", "NC")) {
  F <- filas(TR[g == gg]); L <- inicio(ST[g == gg]); b0 <- llegar(F, L, META[[gg]])
  lk <- F[cur %in% TRANS & nxt %in% TRANS & cur != nxt & p >= 0.02, .(i = cur, j = nxt, p_orig = p)]
  lk[, rel_sube := vapply(seq_len(.N), function(k) 100 * (llegar(modificar(F, i[k], j[k]), L, META[[gg]]) / b0 - 1), 0)]
  lk[, rel_baja := vapply(seq_len(.N), function(k) 100 * (llegar(baja(F, i[k], j[k]), L, META[[gg]]) / b0 - 1), 0)]
  barrido[[gg]] <- lk[, `:=`(g = gg, base = 100 * b0)]
  fg <- F[cur %in% TRANS & nxt == "ABANDONO", .(i = cur, p_orig = p)]
  fg[, rel_fuga := vapply(seq_len(.N), function(k) 100 * (llegar(modificar(F, i[k], "ABANDONO", .1, "fuga"), L, META[[gg]]) / b0 - 1), 0)]
  fugas[[gg]] <- fg[, g := gg] }
barrido <- rbindlist(barrido)[order(g, -rel_sube)]; barrido[, rank := seq_len(.N), by = g]
fugas <- rbindlist(fugas)[order(g, -rel_fuga)]

# ---------------------------------------------------------------- flechas elegidas (con IC por cliente)
ELEG <- list(
  F1 = list(nombre = "Ficha → Carrito (sube)",          interv = 1, i = "PRODUCTO", j = "CARRITO",  tipo = "sube"),
  F2 = list(nombre = "Salida desde Producto (baja)",    interv = 1, i = "PRODUCTO", j = "ABANDONO", tipo = "fuga"),
  F3 = list(nombre = "Carrito → Checkout (sube)",       interv = 2, i = "CARRITO",  j = "CHECKOUT", tipo = "sube"),
  F4 = list(nombre = "Carrito → Producto (baja)",       interv = 2, i = "CARRITO",  j = "PRODUCTO", tipo = "baja"))
clientes <- list(C = sort(unique(h[seg == 1, uid]), method = "radix"), NC = sort(unique(h[seg == 0, uid]), method = "radix"))
mult <- function(n) { M <- matrix(0L, B, n); for (b in 1:B) M[b, ] <- tabulate(sample.int(n, n, TRUE), n); M }
MB <- list(C = mult(length(clientes$C)), NC = mult(length(clientes$NC)))   # mismo orden que fase7_p5_fugas.R
efecto <- function(tr, st, gg, alfa = 0.10) {
  F <- filas(tr); L <- inicio(st); b0 <- llegar(F, L, META[[gg]])
  c(base = b0, sapply(ELEG, function(e) llegar(cambiar(F, e, alfa), L, META[[gg]]))) }
elegidas <- list(); eleg_ic <- list()
for (gg in c("C", "NC")) {
  est <- efecto(TR[g == gg], ST[g == gg], gg)
  u <- clientes[[gg]]; trg <- TR[g == gg]; stg <- ST[g == gg]; it <- match(trg$uid, u); is <- match(stg$uid, u)
  boot <- t(vapply(1:B, function(b) { m <- MB[[gg]][b, ]
    efecto(trg[, .(prev, cur, nxt, N = N * m[it])][N > 0], stg[, .(first, N = N * m[is])][N > 0], gg) }, numeric(length(est))))
  colnames(boot) <- names(est); rel_b <- 100 * (boot[, -1] / boot[, 1] - 1)
  elegidas[[gg]] <- data.table(g = gg, id = names(ELEG), flecha = sapply(ELEG, `[[`, "nombre"), interv = sapply(ELEG, `[[`, "interv"),
    base = 100 * est[["base"]], nuevo = 100 * est[names(ELEG)], rel = 100 * (est[names(ELEG)] / est[["base"]] - 1),
    rel_lo = apply(rel_b, 2, quantile, .025), rel_hi = apply(rel_b, 2, quantile, .975))
  eleg_ic[[gg]] <- data.table(g = gg, base_lo = quantile(100 * boot[, 1], .025), base_hi = quantile(100 * boot[, 1], .975)) }
elegidas <- rbindlist(elegidas); eleg_ic <- rbindlist(eleg_ic)
alfa_sens <- rbindlist(lapply(c("C", "NC"), function(gg) rbindlist(lapply(c(0.05, 0.10, 0.20), function(a) {
  e <- efecto(TR[g == gg], ST[g == gg], gg, a); data.table(g = gg, alfa = 100 * a, id = names(ELEG), rel = 100 * (e[names(ELEG)] / e[["base"]] - 1)) }))))
chequeo_auto <- rbindlist(lapply(c("C", "NC"), function(gg) {
  a <- efecto(TR[g == gg], ST[g == gg], gg); s <- efecto(TRs[g == gg], STs[g == gg], gg)
  data.table(g = gg, medida = c("base", names(ELEG)), con_auto = 100 * a, sin_auto = 100 * s, diferencia = 100 * (a - s)) }))
obs <- h[, .(compra = any(estado == "COMPRA"), chk = any(estado == "CHECKOUT")), by = .(visit_id, g)]
base_tab <- data.table(g = c("C", "NC"), resultado = c("Compra en la visita", "Llega al Checkout"),
  observado = c(100 * obs[g == "C", mean(compra)], 100 * obs[g == "NC", mean(chk)]), modelo = elegidas[id == "F1", base])

# ---------------------------------------------------------------- robustez: compradores solo hasta su 1ª compra
vt <- h[, .(t0 = min(t), compra = any(estado == "COMPRA")), by = .(g, uid, visit_id)]
fc <- vt[g == "C" & compra == TRUE, .(tfc = min(t0)), by = uid]
pre <- merge(vt[g == "C"], fc, by = "uid")[t0 <= tfc, visit_id]
hp <- h[visit_id %in% pre]
TRp <- hp[estado != "COMPRA", .N, by = .(g, uid, prev, cur = estado, nxt)]; STp <- hp[pos == 1L, .N, by = .(g, uid, first = estado)]
Fp <- filas(TRp); Lp <- inicio(STp); bp <- llegar(Fp, Lp, character(0))
lkp <- Fp[cur %in% TRANS & nxt %in% TRANS & cur != nxt & p >= 0.02, .(i = cur, j = nxt, p_orig = p)]
lkp[, rel_sube := vapply(seq_len(.N), function(k) 100 * (llegar(modificar(Fp, i[k], j[k]), Lp, character(0)) / bp - 1), 0)]
robustez_pre <- data.table(visitas_pre = length(pre), visitas_total = vt[g == "C", .N], base = 100 * bp,
  top1 = lkp[order(-rel_sube)][1, paste(i, j)], top2 = lkp[order(-rel_sube)][2, paste(i, j)], peor = lkp[order(rel_sube)][1, paste(i, j)],
  F1 = 100 * (llegar(modificar(Fp, "PRODUCTO", "CARRITO"), Lp, character(0)) / bp - 1),
  F2 = 100 * (llegar(modificar(Fp, "PRODUCTO", "ABANDONO", .1, "fuga"), Lp, character(0)) / bp - 1),
  F3 = 100 * (llegar(modificar(Fp, "CARRITO", "CHECKOUT"), Lp, character(0)) / bp - 1),
  F4 = 100 * (llegar(baja(Fp, "CARRITO", "PRODUCTO"), Lp, character(0)) / bp - 1))

# ---------------------------------------------------------------- B) datos para diseñar las acciones
ratio_ic <- function(num, den, uid, gg) {                         # proporción con IC por cliente (mismos sorteos)
  a <- data.table(uid, num = as.numeric(num), den = as.numeric(den))[, .(n = sum(num), d = sum(den)), by = uid]
  w <- MB[[gg]][, match(a$uid, clientes[[gg]]), drop = FALSE]
  r <- as.vector(w %*% a$n) / as.vector(w %*% a$d)
  c(est = 100 * sum(a$n) / sum(a$d), lo = 100 * quantile(r, .025, names = FALSE), hi = 100 * quantile(r, .975, names = FALSE)) }
fila <- function(gg, medida, x) data.table(g = gg, medida = medida, est = x[["est"]], lo = x[["lo"]], hi = x[["hi"]])
# qué significa cada flecha
h[, pid := fifelse(!is.na(product_id) & grepl("^[0-9]{5,}", product_id), product_id, NA_character_)]
h[, atc_antes := cumsum(shift(estado == "AGREGAR_CARRO", fill = FALSE)) > 0, by = visit_id]
fp <- h[!is.na(pid), .(fp_prod = suppressWarnings(as.double(min(pos[estado == "PRODUCTO"]))), fp_atc = suppressWarnings(as.double(min(pos[estado == "AGREGAR_CARRO"])))), by = .(visit_id, pid)]
h <- merge(h, fp, by = c("visit_id", "pid"), all.x = TRUE, sort = FALSE); setorder(h, visit_id, pos)
h[, nonp := fifelse(estado != "PRODUCTO", pos, NA_integer_)]
h[, sig_pos := nafill(shift(nonp, -1L), "nocb"), by = visit_id]
h[, sig_est := { e <- estado; s <- sig_pos; fifelse(is.na(s), "ABANDONO", e[pmax(s, 1L)]) }, by = visit_id]
h[, prev_est := shift(estado, 1L, fill = "INICIO"), by = visit_id]
flechas <- rbindlist(lapply(c("C", "NC"), function(gg) {
  pc_ <- h[g == gg & estado == "PRODUCTO" & nxt == "CARRITO"]
  cp_ <- h[g == gg & prev_est == "CARRITO" & estado == "PRODUCTO"]
  cpv <- cp_[!is.na(pid)]
  rbind(fila(gg, "Ficha→Carrito: ya agregó algo antes en la misma visita", ratio_ic(pc_$atc_antes, 1, pc_$uid, gg)),
        fila(gg, "Carrito→Ficha: es un producto que ya había visto en la visita", ratio_ic(cpv$fp_prod < cpv$pos, 1, cpv$uid, gg)),
        fila(gg, "Carrito→Ficha: es un producto que ya había agregado en la visita", ratio_ic(is.finite(cpv$fp_atc) & cpv$fp_atc < cpv$pos, 1, cpv$uid, gg)),
        fila(gg, "Después de volver a la ficha: regresa al Carrito", ratio_ic(cp_$sig_est == "CARRITO", 1, cp_$uid, gg)),
        fila(gg, "Después de volver a la ficha: la visita termina sin comprar", ratio_ic(cp_$sig_est == "ABANDONO", 1, cp_$uid, gg))) }))
# qué pasa entre visitas
v <- h[, .(t0 = min(t), compra = any(estado == "COMPRA"), carro = any(estado == "CARRITO"), prod = any(estado == "PRODUCTO"),
           atc = any(estado == "AGREGAR_CARRO")), by = .(g, uid, visit_id)]
setorder(v, uid, t0); v[, k := seq_len(.N), by = uid]; v[, nv := .N, by = uid]
v[, t_sig := { tc <- as.numeric(t0[compra]); vapply(as.numeric(t0), function(x) { y <- tc[tc > x]; if (length(y)) min(y) else NA_real_ }, 0) }, by = uid]
cl <- v[, .(nv = nv[1], k1 = if (any(compra)) min(k[compra]) else NA_integer_, carro = any(carro), prod = any(prod)), by = .(g, uid)]
x <- v[g == "C" & compra == FALSE]; pv <- v[compra == TRUE]
entre_visitas <- rbind(
  fila("C", "Compradores con más de una visita en julio", ratio_ic(cl[g == "C", nv > 1], 1, cl[g == "C", uid], "C")),
  fila("C", "Su 1ª compra no fue en su 1ª visita", ratio_ic(cl[g == "C", k1 > 1], 1, cl[g == "C", uid], "C")),
  fila("C", "Visitas con compra sin 'Agregar al carro' en esa visita", ratio_ic(!pv$atc, 1, pv$uid, "C")),
  fila("C", "Llegó al carro y no pagó: compra en una visita posterior", ratio_ic(x[carro == TRUE, !is.na(t_sig)], 1, x[carro == TRUE, uid], "C")),
  fila("C", "Solo vio fichas y no compró: compra en una visita posterior", ratio_ic(x[carro == FALSE & prod == TRUE, !is.na(t_sig)], 1, x[carro == FALSE & prod == TRUE, uid], "C")),
  fila("NC", "No compradores con más de una visita en julio", ratio_ic(cl[g == "NC", nv > 1], 1, cl[g == "NC", uid], "NC")),
  fila("NC", "No compradores que vieron al menos una ficha", ratio_ic(cl[g == "NC", prod], 1, cl[g == "NC", uid], "NC")),
  fila("NC", "No compradores que llegaron al carro al menos una vez", ratio_ic(cl[g == "NC", carro], 1, cl[g == "NC", uid], "NC")))
dt <- x[carro == TRUE & !is.na(t_sig), .(uid, horas = (t_sig - as.numeric(t0)) / 3600)]
tiempos <- rbind(fila("C", "Compra dentro de 24 horas", ratio_ic(dt$horas <= 24, 1, dt$uid, "C")),
                 fila("C", "Compra dentro de 3 días", ratio_ic(dt$horas <= 72, 1, dt$uid, "C")),
                 fila("C", "Compra dentro de 7 días", ratio_ic(dt$horas <= 168, 1, dt$uid, "C")))
tiempos[, mediana_dias := median(dt$horas) / 24]
curva <- data.table(dias = 0:14)[, pct := sapply(dias, function(z) 100 * mean(dt$horas <= 24 * z))]

# ---------------------------------------------------------------- guardar
barrido[, p_orig := 100 * p_orig]; fugas[, p_orig := 100 * p_orig]   # en % para guardar
r2 <- function(x) { x <- copy(x); for (k in names(x)) if (is.numeric(x[[k]])) set(x, j = k, value = round(x[[k]], 2)); x }
fwrite(r2(barrido), file.path(SALIDA, "p6v2_barrido.csv")); fwrite(r2(fugas), file.path(SALIDA, "p6v2_fugas.csv"))
fwrite(r2(elegidas), file.path(SALIDA, "p6v2_intervenciones.csv")); fwrite(r2(alfa_sens), file.path(SALIDA, "p6v2_sensibilidad_alfa.csv"))
fwrite(r2(chequeo_auto), file.path(SALIDA, "p6v2_chequeos.csv")); fwrite(r2(robustez_pre), file.path(SALIDA, "p6v2_robustez_pre.csv"))
fwrite(r2(flechas), file.path(SALIDA, "p6v2_flechas.csv")); fwrite(r2(rbind(entre_visitas, tiempos, fill = TRUE)), file.path(SALIDA, "p6v2_entre_visitas.csv"))
write_json(list(barrido = r2(barrido), fugas = r2(fugas), elegidas = r2(elegidas), base_ic = r2(eleg_ic), base_tab = r2(base_tab),
                alfa = r2(alfa_sens), chequeo_auto = r2(chequeo_auto), robustez_pre = r2(robustez_pre), flechas = r2(flechas),
                entre_visitas = r2(entre_visitas), tiempos = r2(tiempos), curva = r2(curva), nombres = as.list(NOMBRE)),
           file.path(SALIDA, "p6v2_anexo.json"), auto_unbox = TRUE, digits = NA)

# ---------------------------------------------------------------- figuras
fmt <- function(x, k = 1) formatC(x, format = "f", digits = k, decimal.mark = ",")
COL <- c("Compradores" = "#2a78d6", "No compradores" = "#eb6834"); TXT <- "#0b0b0b"; TXT2 <- "#52514e"; GRID <- "#e6e6e3"
tema <- theme_minimal(base_size = 10.5, base_family = "sans") +
  theme(text = element_text(color = TXT), axis.text = element_text(color = TXT2), panel.grid.major.y = element_blank(),
        panel.grid.minor = element_blank(), panel.grid.major.x = element_line(color = GRID, linewidth = .3),
        strip.text = element_text(face = "bold", hjust = 0, size = 10, color = TXT), legend.position = "none",
        plot.title = element_text(face = "bold", size = 12), plot.subtitle = element_text(color = TXT2, size = 9.5),
        plot.caption = element_text(color = TXT2, size = 8, hjust = 0), plot.title.position = "plot", plot.caption.position = "plot",
        plot.background = element_rect(fill = "white", color = NA))
# impacto de las 4 flechas
f1 <- copy(elegidas); f1[, grupo := factor(fifelse(g == "C", "Compradores", "No compradores"), names(COL))]
f1[, panel := factor(fifelse(g == "C", "Compradores: probabilidad de comprar en la visita", "No compradores: probabilidad de llegar al Checkout"))]
f1[, lab := factor(paste0(interv, ". ", flecha), rev(paste0(sapply(ELEG, `[[`, "interv"), ". ", sapply(ELEG, `[[`, "nombre"))))]
p1 <- ggplot(f1, aes(rel, lab, fill = grupo)) + geom_col(width = .55) +
  geom_errorbarh(aes(xmin = rel_lo, xmax = rel_hi), height = .18, color = TXT2, linewidth = .35) +
  geom_text(aes(x = rel_hi, label = paste0("+", fmt(rel), "%")), hjust = -.25, size = 3.2, color = TXT) +
  facet_wrap(~panel, ncol = 1) + scale_fill_manual(values = COL) +
  scale_x_continuous(labels = function(x) paste0(fmt(x, 0), "%"), expand = expansion(mult = c(0, .18))) +
  labs(title = "Cuánto se mueve el resultado si cada flecha mejora 10%",
       subtitle = "Una flecha a la vez (método de Aung & Kumoi, 2026). 1 = ficha, 2 = carrito. Barras: IC 95% por cliente.",
       x = NULL, y = NULL, caption = "Escenario del modelo, no predicción: el 10% es igual para todas las flechas, para compararlas.\nSe valida con test A/B. No comparar entre paneles: miden resultados distintos.") + tema
ggsave(file.path(SALIDA, "p6v2_fig_impacto.png"), p1, width = 7.6, height = 5.2, dpi = 300)
if (requireNamespace("svglite", quietly = TRUE)) ggsave(file.path(SALIDA, "p6v2_fig_impacto.svg"), p1, width = 7.6, height = 5.2)
# ubicación en el journey (incluye el regreso entre visitas)
nod <- data.table(e = c("PORTADA","BUSQUEDA","PRODUCTO","CARRITO","CHECKOUT","COMPRA"), x = 1:6, y = 0)
nod[, lab := fifelse(e == "BUSQUEDA", "Búsqueda /\nListado", NOMBRE[e])]
mk <- data.table(x = c(3, 4, 3.5), y = c(.95, .95, -1.35), n = c("1", "2", "3"),
                 t = c("Ficha que convence", "Carro para decidir", "Recordatorio entre visitas"))
p2 <- ggplot() + geom_segment(data = nod[-.N], aes(x = x + .38, xend = x + .62, y = 0, yend = 0), color = TXT2,
                              arrow = arrow(length = unit(5, "pt"), type = "closed"), linewidth = .4) +
  annotate("curve", x = 4, xend = 3.05, y = .27, yend = .27, curvature = .55, color = "#b5b4ae", linewidth = .35,
           arrow = arrow(length = unit(4, "pt"), type = "closed")) +
  annotate("text", x = 3.5, y = .62, label = "vuelta atrás", size = 2.6, color = TXT2) +
  geom_tile(data = nod, aes(x, y), width = .76, height = .5, fill = fifelse(nod$e == "COMPRA", "#e8f0fb", "#f4f4f2"), color = "#cfcfca") +
  geom_text(data = nod, aes(x, y, label = lab), size = 3.1, color = TXT, lineheight = .9) +
  annotate("tile", x = 3.5, y = -.85, width = 2.2, height = .32, fill = "#fdf1e9", color = "#e9b993") +
  annotate("text", x = 3.5, y = -.85, label = "Se va sin comprar (Abandono)", size = 2.9, color = TXT) +
  annotate("segment", x = 3, xend = 3, y = -.27, yend = -.69, color = TXT2, linewidth = .35, linetype = "dashed") +
  annotate("segment", x = 4, xend = 4, y = -.27, yend = -.69, color = TXT2, linewidth = .35, linetype = "dashed") +
  annotate("curve", x = 2.4, xend = 1.0, y = -.85, yend = -.3, curvature = -.35, color = "#2a78d6", linewidth = .45,
           arrow = arrow(length = unit(5, "pt"), type = "closed")) +
  annotate("text", x = 1.25, y = -1.2, label = "vuelve otro día", size = 2.7, color = "#2a78d6") +
  geom_point(data = mk, aes(x, y), size = 7, color = "#2a78d6") + geom_text(data = mk, aes(x, y, label = n), color = "white", fontface = "bold", size = 3.4) +
  geom_text(data = mk, aes(x, y + c(.36, .36, -.33), label = t), size = 2.9, color = TXT) +
  annotate("segment", x = 3, xend = 3, y = .78, yend = .29, color = "#2a78d6", linewidth = .4) +
  annotate("segment", x = 4, xend = 4, y = .78, yend = .29, color = "#2a78d6", linewidth = .4) +
  annotate("segment", x = 3.5, xend = 3.5, y = -1.18, yend = -1.02, color = "#2a78d6", linewidth = .4) +
  coord_cartesian(xlim = c(.5, 6.5), ylim = c(-1.85, 1.5)) + theme_void() +
  labs(title = "Dónde se ubican las tres intervenciones") +
  theme(plot.title = element_text(face = "bold", size = 12, color = TXT), plot.background = element_rect(fill = "white", color = NA))
ggsave(file.path(SALIDA, "p6v2_fig_ubicacion.png"), p2, width = 7.6, height = 3.6, dpi = 300)
if (requireNamespace("svglite", quietly = TRUE)) ggsave(file.path(SALIDA, "p6v2_fig_ubicacion.svg"), p2, width = 7.6, height = 3.6)
# cuándo compran después de dejar el carro sin pagar
p3 <- ggplot(curva, aes(dias, pct)) + geom_line(color = "#2a78d6", linewidth = .9) + geom_point(color = "#2a78d6", size = 2.2) +
  geom_text(data = curva[dias %in% c(1, 3, 7)], aes(label = paste0(fmt(pct, 0), "%")), vjust = -1, size = 3.2, color = TXT) +
  scale_x_continuous(breaks = c(0, 1, 3, 7, 14), labels = function(x) paste(x, "d")) +
  scale_y_continuous(limits = c(0, 100), labels = function(x) paste0(x, "%")) +
  labs(title = "Cuándo compran después de dejar el carro sin pagar",
       subtitle = "Compradores: visitas que llegaron al carro sin comprar y luego tuvieron una compra. % acumulado de esas compras.",
       x = "Días desde la visita con carro sin pagar", y = NULL,
       caption = "Tiempo entre el inicio de ambas visitas (date_time_start). Confirmar con Falabella la confiabilidad de las horas.") +
  tema + theme(panel.grid.major.y = element_line(color = GRID, linewidth = .3))
ggsave(file.path(SALIDA, "p6v2_fig_tiempo.png"), p3, width = 7.6, height = 3.8, dpi = 300)
if (requireNamespace("svglite", quietly = TRUE)) ggsave(file.path(SALIDA, "p6v2_fig_tiempo.svg"), p3, width = 7.6, height = 3.8)

cat("\n== Barrido top 4 y peores 2 ==\n"); print(r2(barrido[, rbind(head(.SD, 4), tail(.SD, 2)), by = g][, .(g, i, j, p = p_orig, rel_sube, rel_baja)]))
cat("\n== Fugas ==\n"); print(r2(fugas[, head(.SD, 3), by = g]))
cat("\n== Flechas elegidas ==\n"); print(r2(elegidas)); print(r2(eleg_ic)); print(r2(base_tab))
cat("\n== Sensibilidad alfa ==\n"); print(dcast(r2(alfa_sens), g + id ~ alfa, value.var = "rel"))
cat("\n== Con vs sin autotransiciones ==\n"); print(r2(chequeo_auto))
cat("\n== Robustez pre-1a compra ==\n"); print(r2(robustez_pre))
cat("\n== Qué significa cada flecha ==\n"); print(r2(flechas))
cat("\n== Entre visitas ==\n"); print(r2(entre_visitas)); print(r2(tiempos))
