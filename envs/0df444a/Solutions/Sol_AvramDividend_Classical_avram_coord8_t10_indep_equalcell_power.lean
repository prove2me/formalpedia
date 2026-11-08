-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord8_t10_indep_equalcell_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:32:58.576165+00:00
-- url     : https://prove2.me/submissions/5ef0f6b3-d2cb-4e9b-b647-553b381d5665

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Independent cell products with identical means have power-factorised expectation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (C : Fin (n + 1) → Ω → ℝ) (F : Ω → ℝ)
    (hIndep : iIndepFun C μ)
    (hMeas : ∀ i, AEStronglyMeasurable (C i) μ)
    (hSame : ∀ i, (∫ ω, C i ω ∂μ) = ∫ ω, F ω ∂μ) :
    (∫ ω, ∏ i : Fin (n + 1), C i ω ∂μ) =
      (∫ ω, F ω ∂μ) ^ (n + 1) := by
  calc
    (∫ ω, ∏ i : Fin (n + 1), C i ω ∂μ) =
        ∏ i : Fin (n + 1), (∫ ω, C i ω ∂μ) := by
          simpa only [Finset.prod_apply] using
            (hIndep.integral_prod_eq_prod_integral hMeas)
    _ = (∫ ω, F ω ∂μ) ^ (n + 1) := by
      simp [hSame]
