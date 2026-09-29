-- Prove2me | solution 1 for FamousTheorems.hofer_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:24:53.040628+00:00
-- url     : https://prove2.me/submissions/d0efd528-dd2b-4164-826f-d272834c7309

import Mathlib

theorem solution {X : Type*} [MetricSpace X] [CompleteSpace X] (x : X) {ε : ℝ} (ε_pos : 0 < ε) {ϕ : X → ℝ}
    (cont : Continuous ϕ) (nonneg : ∀ y, 0 ≤ ϕ y) :
    ∃ ε' > 0, ∃ x' : X, ε' ≤ ε ∧ dist x' x ≤ 2 * ε ∧ ε * ϕ x ≤ ε' * ϕ x' ∧
      ∀ y, dist x' y ≤ ε' → ϕ y ≤ 2 * ϕ x' :=
  hofer x ε ε_pos cont nonneg
