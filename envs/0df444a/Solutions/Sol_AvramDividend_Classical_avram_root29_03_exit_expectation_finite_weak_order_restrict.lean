-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_exit_expectation_finite_weak_order_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:17:31.809997+00:00
-- url     : https://prove2.me/submissions/4c121f10-1c18-4cc2-8043-b2b3b7bffba2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_strict_up_event_iff_finite_weak_order
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_expectation_eq_restrict_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- On paths with a finite upper clock, weak upper-first order agrees with
the genuine strict exit event, even inside the original-law lintegral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) (ha : 0 < a) :
    twoSidedExitExpectation X q a x =
      (∫⁻ ω in {ω : Ω |
        twoSidedExitUpTime X (a - x) ω ≤ twoSidedExitDownTime X (-x) ω ∧
        twoSidedExitUpTime X (a - x) ω < ⊤},
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) ∂P) := by
  have hEvent :
      {ω : Ω | twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω} =
      {ω : Ω | twoSidedExitUpTime X (a - x) ω ≤
          twoSidedExitDownTime X (-x) ω ∧
          twoSidedExitUpTime X (a - x) ω < ⊤} := by
    ext ω
    exact avram_root29_03_strict_up_event_iff_finite_weak_order
      X a x ha ω
  rw [avram_root29_03_exit_expectation_eq_restrict_lintegral X q a x, hEvent]
