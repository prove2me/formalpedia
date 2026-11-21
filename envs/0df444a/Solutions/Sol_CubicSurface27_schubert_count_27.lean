-- Prove2me | solution 1 for CubicSurface27.schubert_count_27
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:18:16.197543+00:00
-- url     : https://prove2.me/submissions/4213d74f-d187-4bb7-bd7e-09a66e56637d

import Mathlib

theorem solution {R : Type*} [CommRing R] (σ10 σ20 σ11 σ22 : R)
    (h_sq : σ10 ^ 2 = σ20 + σ11)
    (h_orth : σ11 * σ20 = 0)
    (h_pt : σ11 ^ 2 = σ22) :
    9 * σ11 * (2 * σ10 ^ 2 + σ11) = 27 * σ22 := by
  linear_combination 18 * σ11 * h_sq + 18 * h_orth + 27 * h_pt
