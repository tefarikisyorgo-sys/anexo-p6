# =====================================================================
# fase8_p6_intervenciones.R  ·  Pregunta 6: ¿qué 2-3 intervenciones de marketing/CRO priorizar
#                               para mover clientes hacia la compra, y en qué estado ubicarlas?
#
# MÉTODO: el de Aung & Kumoi (2026, IEEE Access, sec. III-F y III-G), sobre la misma cadena de P4
# (orden 1, con autotransiciones, visitas cortadas en su 1ª compra, Abandono al final de las visitas sin compra).
#   1) Barrido: se prueba UNA modificación a la vez en cada enlace entre estados (no se elige a dedo).
#      - "sube":  la probabilidad i -> j sube 10% relativo (ej. 0,40 -> 0,44). Esa masa se descuenta de las otras
#                 salidas de i hacia estados de navegación, en proporción a su tamaño. No se tocan la autotransición
#                 ni la salida a Compra/Abandono (igual que el paper).
#      - "fuga":  la probabilidad i -> Abandono baja 10% relativo y esa masa se reparte, en proporción, en las otras
#                 salidas de i hacia estados de navegación (sin autotransición). Es la misma fórmula aplicada al
#                 enlace de salida (el paper también lee el cambio en Exit, delta_m+1).
#      - Impacto: delta = l'(B' - B) (paper, ec. 5). l = estados de entrada de las visitas; B = probabilidad de
#        terminar en el resultado. Compradores: probabilidad de compra por visita. No compradores: no compran en
#        julio por definición, así que se mide cuánto avanzan: probabilidad de llegar al Checkout (último paso
#        antes de comprar).
#   2) Se repite el barrido con orden 2 (estado anterior + actual) para ver si el ranking cambia.
#   3) Para las intervenciones elegidas: IC 95% (bootstrap por cliente, 500 réplicas, mismos clientes sorteados
#      que fase7_p5_fugas.R), sensibilidad al tamaño del cambio (5%, 10%, 20%), escenario combinado y chequeo
#      con vs sin autotransiciones (debe dar idéntico: B solo depende de las salidas de cada estado).
#   4) Prueba de memoria por estado (M.1, prueba C), para explicar cómo se calculó: para cada estado, cuánto cambia
#      la distribución del siguiente paso si además se sabe de dónde venía (distancia de variación total entre
#      orden 2 y orden 1, promedio ponderado por cuántas veces se llega desde cada estado anterior).
#
# NO MODIFICA df_falabella_estados ni df_markov (trabaja sobre una copia: d).
# OBJETOS QUE CREA: d, h, TR, ST, TRs, STs, clientes, MB, barrido, elegidas, eleg_ic, alfa_sens, chequeo_auto,
#                   base_tab, memoria (y funciones: filas, inicio, modificar, llegar, aplicar).
# ARCHIVOS QUE GUARDA (carpeta "resultados_p6", al lado de donde se corre el script):
#   p6_barrido.csv, p6_intervenciones.csv, p6_sensibilidad_alfa.csv, p6_chequeos.csv, p6_memoria.csv,
#   p6_anexo.json, p6_fig_impacto.png/.svg, p6_fig_ubicacion.png/.svg
# PAQUETES: data.table, jsonlite, ggplot2 (y svglite para los .svg). Tiempo aproximado: 2-4 minutos.
# =====================================================================
suppressMessages({library(data.table); library(jsonlite); library(ggplot2)})
set.seed(2026)
B <- 500
SALIDA <- "resultados_p6"; dir.create(SALIDA, showWarnings = FALSE)
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
           t = date_time_start, estado)]
setorder(h, visit_id, dia, node_order, t); h[, pos := seq_len(.N), by = visit_id]
h[, pc := if (any(estado == "COMPRA")) min(pos[estado == "COMPRA"]) else NA_integer_, by = visit_id]
h <- h[is.na(pc) | pos <= pc]; h[, g := fifelse(seg == 1, "C", "NC")]
h[, `:=`(prev = shift(estado, 1L, fill = "INICIO"), nxt = shift(estado, -1L, fill = "ABANDONO")), by = visit_id]
TR <- h[estado != "COMPRA", .N, by = .(g, uid, prev, cur = estado, nxt)]
ST <- h[pos == 1L, .N, by = .(g, uid, first = estado)]
# versión sin autotransiciones (clics seguidos en el mismo estado se juntan)
hs <- h[, .(g, uid, visit_id, estado)][, keep := estado != shift(estado, fill = ""), by = visit_id][keep == TRUE]
hs[, `:=`(prev = shift(estado, 1L, fill = "INICIO"), nxt = shift(estado, -1L, fill = "ABANDONO")), by = visit_id]
TRs <- hs[estado != "COMPRA", .N, by = .(g, uid, prev, cur = estado, nxt)]
STs <- hs[, .SD[1], by = visit_id][, .N, by = .(g, uid, first = estado)]

# ---------------------------------------------------------------- funciones
filas <- function(tr, orden) {
  x <- if (orden == 1) tr[, .(N = sum(N)), by = .(key = cur, cur, nxt)] else
    tr[, .(N = sum(N)), by = .(key = paste(prev, cur, sep = "|"), cur, nxt)]
  x[, p := N / sum(N), by = key][] }
inicio <- function(st, orden) {
  x <- st[, .(N = sum(N)), by = first]; x[, key := if (orden == 1) first else paste("INICIO", first, sep = "|")]
  x[, p := N / sum(N)][] }
modificar <- function(F, i, j, alfa = 0.10, tipo = "sube") {
  F <- copy(F); F[, mod := cur == i]
  if (tipo == "sube") {
    F[mod == TRUE, elig := !(nxt %in% c(ABS, i, j))]
    F[mod == TRUE, `:=`(masa = alfa * sum(p[nxt == j]), base = sum(p[elig])), by = key]
    F[mod == TRUE & nxt == j & base > 0, p := p * (1 + alfa)]
  } else {
    F[mod == TRUE, elig := !(nxt %in% c(ABS, i))]
    F[mod == TRUE, `:=`(masa = alfa * sum(p[nxt == "ABANDONO"]), base = sum(p[elig])), by = key]
    F[mod == TRUE & nxt == "ABANDONO" & base > 0, p := p * (1 - alfa)]
  }
  sg <- if (tipo == "sube") -1 else 1                      # sube: se descuenta de las otras; fuga: se les suma
  F[mod == TRUE & elig == TRUE & base > 0, p := p + sg * masa * p / base]
  F[, c("mod", "elig", "masa", "base") := NULL][] }
aplicar <- function(F, lista, alfa = 0.10) { for (z in lista) F <- modificar(F, z$i, z$j, alfa, z$tipo); F }
llegar <- function(F, L, meta, orden) {                     # probabilidad de llegar a 'meta' desde la entrada
  fin <- c(ABS, meta); F <- F[!(cur %in% meta)]
  F[, dest := fifelse(nxt %in% fin, nxt, if (orden == 1) nxt else paste(cur, nxt, sep = "|"))]
  S <- unique(F$key)
  Q <- matrix(0, length(S), length(S), dimnames = list(S, S)); R <- matrix(0, length(S), length(fin), dimnames = list(S, fin))
  q <- F[dest %in% S]; r <- F[dest %in% fin]
  Q[cbind(match(q$key, S), match(q$dest, S))] <- q$p
  r <- r[, .(p = sum(p)), by = .(key, dest)]; R[cbind(match(r$key, S), match(r$dest, fin))] <- r$p
  Bm <- solve(diag(length(S)) - Q, R)                        # B = (I - Q)^-1 R
  L <- copy(L); L[, dest := fifelse(first %in% fin, first, key)]
  lt <- L[dest %in% S]; la <- L[dest %in% fin]
  out <- colSums(Bm[lt$dest, , drop = FALSE] * lt$p); out[la$dest] <- out[la$dest] + la$p
  sum(out[if (length(meta)) meta else "COMPRA"]) }
META <- list(C = character(0), NC = "CHECKOUT")
fmt <- function(x, k = 1) formatC(x, format = "f", digits = k, decimal.mark = ",")

# ---------------------------------------------------------------- 1-2) barrido de enlaces, orden 1 y 2
barrido <- list()
for (gg in c("C", "NC")) {
  F1 <- filas(TR[g == gg], 1)
  links <- rbind(F1[cur %in% TRANS & nxt %in% TRANS & cur != nxt & p >= 0.02, .(i = cur, j = nxt, p_orig = p, tipo = "sube")],
                 F1[cur %in% TRANS & nxt == "ABANDONO", .(i = cur, j = "ABANDONO", p_orig = p, tipo = "fuga")])
  for (o in 1:2) {
    F <- filas(TR[g == gg], o); L <- inicio(ST[g == gg], o); base <- llegar(F, L, META[[gg]], o)
    links[, paste0("nuevo_O", o) := vapply(seq_len(.N), function(k) llegar(modificar(F, i[k], j[k], 0.10, tipo[k]), L, META[[gg]], o), 0)]
    links[, paste0("base_O", o) := base] }
  barrido[[gg]] <- links[, g := gg] }
barrido <- rbindlist(barrido)
barrido[, `:=`(rel_O1 = 100 * (nuevo_O1 / base_O1 - 1), rel_O2 = 100 * (nuevo_O2 / base_O2 - 1),
               pp_O1 = 100 * (nuevo_O1 - base_O1), pp_O2 = 100 * (nuevo_O2 - base_O2))]
barrido[, `:=`(rank_O1 = frank(-rel_O1, ties.method = "min"), rank_O2 = frank(-rel_O2, ties.method = "min")), by = g]
spear <- barrido[, .(spearman = cor(rel_O1, rel_O2, method = "spearman"), enlaces = .N,
                     top3_iguales = setequal(head(.SD[order(-rel_O1)], 3)[, paste(i, j)], head(.SD[order(-rel_O2)], 3)[, paste(i, j)])), by = g]
setorder(barrido, g, rank_O1)

# ---------------------------------------------------------------- 3) intervenciones elegidas
# Criterio: top 3 del barrido en ambos grupos y ambos órdenes + respaldo en P5 + factibilidad.
ELEG <- list(
  I1 = list(nombre = "Retener en la ficha", i = "PRODUCTO", j = "ABANDONO", tipo = "fuga"),
  I2 = list(nombre = "De la ficha al carro", i = "PRODUCTO", j = "CARRITO", tipo = "sube"),
  I3 = list(nombre = "Del carro al pago", i = "CARRITO", j = "CHECKOUT", tipo = "sube"))
ESC <- c(lapply(ELEG, function(z) list(z)), list(I123 = unname(ELEG)))
NOMESC <- c(sapply(ELEG, `[[`, "nombre"), I123 = "Las tres juntas")
clientes <- list(C = sort(unique(h[seg == 1, uid]), method = "radix"), NC = sort(unique(h[seg == 0, uid]), method = "radix"))
mult <- function(n) { M <- matrix(0L, B, n); for (b in 1:B) M[b, ] <- tabulate(sample.int(n, n, TRUE), n); M }
MB <- list(C = mult(length(clientes$C)), NC = mult(length(clientes$NC)))   # mismo orden que fase7_p5_fugas.R
efecto <- function(tr, st, gg, orden = 1, alfa = 0.10) {
  F <- filas(tr, orden); L <- inicio(st, orden); b0 <- llegar(F, L, META[[gg]], orden)
  c(base = b0, sapply(ESC, function(e) llegar(aplicar(F, e, alfa), L, META[[gg]], orden))) }
elegidas <- list(); eleg_ic <- list()
for (gg in c("C", "NC")) {
  est <- efecto(TR[g == gg], ST[g == gg], gg, 1); est2 <- efecto(TR[g == gg], ST[g == gg], gg, 2)
  u <- clientes[[gg]]; trg <- TR[g == gg]; stg <- ST[g == gg]; it <- match(trg$uid, u); is <- match(stg$uid, u)
  boot <- t(vapply(1:B, function(b) { m <- MB[[gg]][b, ]
    efecto(trg[, .(prev, cur, nxt, N = N * m[it])][N > 0], stg[, .(first, N = N * m[is])][N > 0], gg, 1) }, numeric(length(est))))
  colnames(boot) <- names(est)
  rel_b <- 100 * (boot[, -1] / boot[, 1] - 1); pp_b <- 100 * (boot[, -1] - boot[, 1])
  elegidas[[gg]] <- data.table(g = gg, esc = names(ESC), intervencion = NOMESC[names(ESC)],
    base = 100 * est[["base"]], nuevo = 100 * est[names(ESC)],
    pp = 100 * (est[names(ESC)] - est[["base"]]), pp_lo = apply(pp_b, 2, quantile, .025), pp_hi = apply(pp_b, 2, quantile, .975),
    rel = 100 * (est[names(ESC)] / est[["base"]] - 1), rel_lo = apply(rel_b, 2, quantile, .025), rel_hi = apply(rel_b, 2, quantile, .975),
    base_O2 = 100 * est2[["base"]], rel_O2 = 100 * (est2[names(ESC)] / est2[["base"]] - 1))
  eleg_ic[[gg]] <- data.table(g = gg, base_lo = quantile(100 * boot[, 1], .025), base_hi = quantile(100 * boot[, 1], .975)) }
elegidas <- rbindlist(elegidas); eleg_ic <- rbindlist(eleg_ic)
alfa_sens <- rbindlist(lapply(c("C", "NC"), function(gg) rbindlist(lapply(c(0.05, 0.10, 0.20), function(a) {
  e <- efecto(TR[g == gg], ST[g == gg], gg, 1, a); data.table(g = gg, alfa = 100 * a, esc = names(ESC), rel = 100 * (e[names(ESC)] / e[["base"]] - 1)) }))))
chequeo_auto <- rbindlist(lapply(c("C", "NC"), function(gg) {
  a <- efecto(TR[g == gg], ST[g == gg], gg, 1); s <- efecto(TRs[g == gg], STs[g == gg], gg, 1)
  data.table(g = gg, medida = c("base", names(ESC)), con_auto = 100 * a, sin_auto = 100 * s, diferencia = 100 * (a - s)) }))
obs <- h[, .(compra = any(estado == "COMPRA"), chk = any(estado == "CHECKOUT")), by = .(visit_id, g)]
base_tab <- data.table(g = c("C", "NC"), resultado = c("Compra en la visita", "Llega al Checkout"),
  observado = c(100 * obs[g == "C", mean(compra)], 100 * obs[g == "NC", mean(chk)]),
  orden1 = elegidas[esc == "I1", base], orden2 = elegidas[esc == "I1", base_O2])

# ---------------------------------------------------------------- 4) prueba de memoria por estado (M.1, prueba C)
memoria_fun <- function(tr, minn = 100) {
  p1 <- tr[, .(N = sum(N)), by = .(g, cur, nxt)][, p1 := N / sum(N), by = .(g, cur)][, N := NULL]
  p2 <- tr[, .(N = sum(N)), by = .(g, prev, cur, nxt)][, n2 := sum(N), by = .(g, prev, cur)][, p2 := N / n2]
  x <- merge(p2, p1, by = c("g", "cur", "nxt"), all = TRUE)
  todos <- unique(x[!is.na(prev), .(g, prev, cur, n2)])
  full <- merge(todos, unique(p1[, .(g, cur, nxt)]), by = c("g", "cur"), allow.cartesian = TRUE)
  full <- merge(full, p2[, .(g, prev, cur, nxt, p2)], by = c("g", "prev", "cur", "nxt"), all.x = TRUE)
  full <- merge(full, p1, by = c("g", "cur", "nxt"), all.x = TRUE); full[is.na(p2), p2 := 0]; full[is.na(p1), p1 := 0]
  s <- full[n2 >= minn, .(tv = 50 * sum(abs(p2 - p1)), n2 = n2[1]), by = .(g, cur, prev)]
  s[, .(memoria_pp = sum(tv * n2) / sum(n2), max_pp = max(tv), anteriores = .N), by = .(g, cur)] }
memoria <- merge(memoria_fun(TR)[, .(g, cur, con_auto = memoria_pp)], memoria_fun(TRs)[, .(g, cur, sin_auto = memoria_pp)], by = c("g", "cur"))
setorder(memoria, g, -con_auto)

# ---------------------------------------------------------------- guardar
r2 <- function(x) { x <- copy(x); for (k in names(x)) if (is.numeric(x[[k]])) set(x, j = k, value = round(x[[k]], 2)); x }
fwrite(r2(barrido), file.path(SALIDA, "p6_barrido.csv")); fwrite(r2(elegidas), file.path(SALIDA, "p6_intervenciones.csv"))
fwrite(r2(alfa_sens), file.path(SALIDA, "p6_sensibilidad_alfa.csv"))
fwrite(r2(rbind(chequeo_auto, fill = TRUE)), file.path(SALIDA, "p6_chequeos.csv")); fwrite(r2(memoria), file.path(SALIDA, "p6_memoria.csv"))
write_json(list(barrido = r2(barrido), spearman = r2(spear), elegidas = r2(elegidas), base_ic = r2(eleg_ic), base_tab = r2(base_tab),
                alfa = r2(alfa_sens), chequeo_auto = r2(chequeo_auto), memoria = r2(memoria), nombres = as.list(NOMBRE)),
           file.path(SALIDA, "p6_anexo.json"), auto_unbox = TRUE, digits = NA)

# ---------------------------------------------------------------- figuras
COL <- c("Compradores" = "#2a78d6", "No compradores" = "#eb6834"); TXT <- "#0b0b0b"; TXT2 <- "#52514e"; GRID <- "#e6e6e3"
tema <- theme_minimal(base_size = 10.5, base_family = "sans") +
  theme(text = element_text(color = TXT), axis.text = element_text(color = TXT2), panel.grid.major.y = element_blank(),
        panel.grid.minor = element_blank(), panel.grid.major.x = element_line(color = GRID, linewidth = .3),
        strip.text = element_text(face = "bold", hjust = 0, size = 10, color = TXT), legend.position = "none",
        plot.title = element_text(face = "bold", size = 12), plot.subtitle = element_text(color = TXT2, size = 9.5),
        plot.caption = element_text(color = TXT2, size = 8, hjust = 0), plot.title.position = "plot",
        plot.background = element_rect(fill = "white", color = NA))
f1 <- copy(elegidas); f1[, grupo := factor(fifelse(g == "C", "Compradores", "No compradores"), names(COL))]
f1[, panel := factor(fifelse(g == "C", "Compradores: probabilidad de comprar en la visita", "No compradores: probabilidad de llegar al Checkout"))]
f1[, lab := factor(intervencion, rev(NOMESC))]
p1 <- ggplot(f1, aes(rel, lab, fill = grupo)) + geom_col(width = .55) +
  geom_errorbarh(aes(xmin = rel_lo, xmax = rel_hi), height = .18, color = TXT2, linewidth = .35) +
  geom_text(aes(x = rel_hi, label = paste0("+", fmt(rel), "%")), hjust = -.25, size = 3.2, color = TXT) +
  facet_wrap(~panel, ncol = 1) + scale_fill_manual(values = COL) +
  scale_x_continuous(labels = function(x) paste0(fmt(x, 0), "%"), expand = expansion(mult = c(0, .18))) +
  labs(title = "Impacto simulado de cada intervención (cambio relativo)",
       subtitle = "Cada intervención mueve un 10% su enlace (método de Aung & Kumoi, 2026). Barras: IC 95% por cliente.",
       x = NULL, y = NULL, caption = "Escenario del modelo (orden 1), no causalidad: debe validarse con un test A/B.") + tema
ggsave(file.path(SALIDA, "p6_fig_impacto.png"), p1, width = 7.6, height = 5.0, dpi = 300)
if (requireNamespace("svglite", quietly = TRUE)) ggsave(file.path(SALIDA, "p6_fig_impacto.svg"), p1, width = 7.6, height = 5.0)
# ubicación en el journey
nod <- data.table(e = c("PORTADA","BUSQUEDA","PRODUCTO","CARRITO","CHECKOUT","COMPRA"), x = c(1, 2, 3, 4, 5, 6), y = 0)
nod[, lab := fifelse(e == "BUSQUEDA", "Búsqueda /\nListado", NOMBRE[e])]
mk <- data.table(x = c(3, 3.5, 4.5), y = c(-0.9, 0.85, 0.85), n = c("1", "2", "3"),
                 t = c("Retener en la ficha\n(baja la salida desde Producto)", "De la ficha al carro", "Del carro al pago"))
p2 <- ggplot() + geom_segment(data = nod[-.N], aes(x = x + .38, xend = x + .62, y = 0, yend = 0), color = TXT2,
                              arrow = arrow(length = unit(5, "pt"), type = "closed"), linewidth = .4) +
  geom_tile(data = nod, aes(x, y), width = .76, height = .5, fill = fifelse(nod$e == "COMPRA", "#e8f0fb", "#f4f4f2"), color = "#cfcfca") +
  geom_text(data = nod, aes(x, y, label = lab), size = 3.1, color = TXT, lineheight = .9) +
  geom_point(data = mk, aes(x, y), size = 7, color = "#2a78d6") + geom_text(data = mk, aes(x, y, label = n), color = "white", fontface = "bold", size = 3.4) +
  geom_text(data = mk, aes(x + c(0, 0, 0), y + c(-.42, .38, .38), label = t), size = 2.9, color = TXT, lineheight = .9) +
  annotate("segment", x = 3.5, xend = 3.5, y = .62, yend = .3, color = "#2a78d6", linewidth = .4) +
  annotate("segment", x = 4.5, xend = 4.5, y = .62, yend = .3, color = "#2a78d6", linewidth = .4) +
  annotate("segment", x = 3, xend = 3, y = -.62, yend = -.27, color = "#2a78d6", linewidth = .4) +
  coord_cartesian(xlim = c(.5, 6.5), ylim = c(-1.55, 1.45)) + theme_void() +
  labs(title = "Dónde se ubican las tres intervenciones en el journey") +
  theme(plot.title = element_text(face = "bold", size = 12, color = TXT), plot.background = element_rect(fill = "white", color = NA))
ggsave(file.path(SALIDA, "p6_fig_ubicacion.png"), p2, width = 7.6, height = 3.0, dpi = 300)
if (requireNamespace("svglite", quietly = TRUE)) ggsave(file.path(SALIDA, "p6_fig_ubicacion.svg"), p2, width = 7.6, height = 3.0)

cat("\n== Spearman orden 1 vs 2 ==\n"); print(r2(spear))
cat("\n== Top 8 del barrido ==\n"); print(r2(barrido[rank_O1 <= 8, .(g, tipo, i, j, p_orig = 100 * p_orig, rel_O1, rel_O2, rank_O1, rank_O2)]))
cat("\n== Intervenciones elegidas ==\n"); print(r2(elegidas)); print(r2(eleg_ic))
cat("\n== Base: observado vs modelo ==\n"); print(r2(base_tab))
cat("\n== Sensibilidad alfa ==\n"); print(dcast(r2(alfa_sens), g + esc ~ alfa, value.var = "rel"))
cat("\n== Con vs sin autotransiciones ==\n"); print(r2(chequeo_auto))
cat("\n== Memoria por estado (pp) ==\n"); print(r2(memoria))
