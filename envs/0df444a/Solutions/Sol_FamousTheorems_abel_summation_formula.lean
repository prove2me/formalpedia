-- Prove2me | solution 1 for FamousTheorems.abel_summation_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:59:21.358286+00:00
-- url     : https://prove2.me/submissions/8f159c13-73e5-44d8-bcfd-801364fc6cda

import Mathlib

theorem solution {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} {b : ℝ} (hb : 0 ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc 0 b, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 0 b)) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, f k * c k =
      f b * ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k - ∫ t in Set.Ioc 0 b, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k :=
  sum_mul_eq_sub_integral_mul c hb hf_diff hf_int
