-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_named_exit_survives_horizon_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:15:24.999145+00:00
-- url     : https://prove2.me/submissions/a77a1b34-a56e-4ea8-a89e-3967c433bd92

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_first_named_exit_lt_horizon_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Survival without a strict two-sided exit before a fixed finite
horizon is a measurable event, including equality at the horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | (T : ℝ≥0∞) ≤
        min (twoSidedExitUpTime X upper ω)
          (twoSidedExitDownTime X lower ω)} := by
  have hExit :=
    chat03_first_named_exit_lt_horizon_measurable X lower upper T
  have hEq :
      {ω : Ω | (T : ℝ≥0∞) ≤
        min (twoSidedExitUpTime X upper ω)
          (twoSidedExitDownTime X lower ω)} =
      {ω : Ω | ¬ min (twoSidedExitUpTime X upper ω)
        (twoSidedExitDownTime X lower ω) < (T : ℝ≥0∞)} := by
    ext ω
    simp only [Set.mem_setOf_eq, not_lt]
  rw [hEq]
  exact hExit.compl
