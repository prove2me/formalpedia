-- Prove2me | solution 1 for FamousTheorems.kronecker_roots_of_unity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:59:29.608246+00:00
-- url     : https://prove2.me/submissions/3f890b9f-d7e9-4fd2-9bdf-b46c071d0b82

import Mathlib

theorem solution (K : Type*) [Field K] [NumberField K] {x : K} (hx₀ : x ≠ 0) (hxi : IsIntegral ℤ x)
    (hx : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ 1) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 :=
  (NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hx₀ hxi hx).imp fun _ ⟨hn, h⟩ => ⟨hn, h⟩
