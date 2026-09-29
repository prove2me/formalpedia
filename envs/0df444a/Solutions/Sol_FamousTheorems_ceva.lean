-- Prove2me | solution 1 for FamousTheorems.ceva
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T22:53:52.448799+00:00
-- url     : https://prove2.me/submissions/064a59fe-0401-4e63-b785-fbb9e5b96d73

import Mathlib

open scoped Affine

theorem solution {𝕜 V P : Type*} [SeminormedAddCommGroup V] [NormedField 𝕜] [NormedSpace 𝕜 V]
    [MetricSpace P] [NormedAddTorsor V P] {t : Affine.Triangle 𝕜 P} {p : Fin 3 → P} {p' : P}
    (hp0 : ∀ i, p i ≠ t.points (i + 2))
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hp' : ∀ i : Fin 3, p' ∈ line[𝕜, t.points i, p i]) :
    ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by
  exact Affine.Triangle.prod_dist_div_dist_eq_one_of_mem_line_of_mem_line hp0 hp hp'
