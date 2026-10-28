-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_zero_limit_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:12:01.711994+00:00
-- url     : https://prove2.me/submissions/d3de7790-82ee-4e34-b67c-a49fb4fb642c

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_piecewise_lipschitz_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The q-to-zero scale-function error is at most linear in nonnegative q. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, ∀ q ∈ Icc (0 : ℝ) Q,
      |W q x - W 0 x| ≤ q *
        (if 0 < x then ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) else 0) := by
  intro x q hq
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) Q := ⟨le_rfl, hQ⟩
  have hb := unbounded_scale_discount_family_piecewise_lipschitz_bound
    X hnbv Q hQ W hW x 0 hzero q hq
  simpa only [sub_zero, abs_of_nonneg hq.1] using hb
