-- Prove2me | solution 1 for FamousTheorems.cstar_algebra_sum_four_unitaries_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:42:11.322217+00:00
-- url     : https://prove2.me/submissions/a620bea5-50a6-4fd7-9137-95c599cf8f85

import Mathlib

theorem solution {A : Type*} [CStarAlgebra A] (x : A) :
    ∃ (u : Fin 4 → unitary A) (c : Fin 4 → ℂ), x = ∑ i : Fin 4, c i • (u i : A) ∧ ∀ i, ‖c i‖ ≤ ‖x‖ / 2 :=
  CStarAlgebra.exists_sum_four_unitary x
