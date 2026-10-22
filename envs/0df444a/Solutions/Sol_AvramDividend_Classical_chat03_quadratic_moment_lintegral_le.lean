-- Prove2me | solution 1 for AvramDividend.Classical.chat03_quadratic_moment_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:41:17.854183+00:00
-- url     : https://prove2.me/submissions/5ff03a9f-4917-4135-afbb-46716f770192

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-!
Turn a real-valued upper bound on an integrable quadratic moment into a
bound on its nonnegative Lebesgue integral, preserving the same constant.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (C : ℝ)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P ∧
      ∫ ω, (Y ω) ^ 2 ∂P ≤ C) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) ≤ ENNReal.ofReal C := by
  have hnonneg : 0 ≤ᵐ[P] (fun ω => (Y ω) ^ 2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω))
  rw [← ofReal_integral_eq_lintegral_ofReal hY2.1 hnonneg]
  exact ENNReal.ofReal_le_ofReal hY2.2
