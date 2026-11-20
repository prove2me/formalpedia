-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_joint_tube_and_size2_mark_same_short_clock_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:48:20.921848+00:00
-- url     : https://prove2.me/submissions/bb4f5d5a-a93d-414b-97e3-dd775326e738

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_positive_long_centered_brownian_tube
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_mark_positive_before_any_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {ΩB ΩJ : Type*} [MeasurableSpace ΩB] [MeasurableSpace ΩJ]
    (μB : Measure ΩB) [IsProbabilityMeasure μB]
    (μJ : Measure ΩJ)
    (B : ΩB → C(unitInterval, ℝ))
    (hB : GlynnSTS.Limit.IsStdBMC μB B)
    (τ Y : ℕ → ΩJ → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μJ) :
    0 < (μB.prod μJ)
      ({ω : ΩB | ∀ s : unitInterval,
          s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
            |B ω s| < (1 / 4000 : ℝ)} ×ˢ
       {ω : ΩJ | τ 0 ω ≤ (1 / 500 : ℝ)}) := by
  letI : IsProbabilityMeasure μJ := hJ.indep.isProbabilityMeasure
  have hBrown : 0 < μB
      {ω : ΩB | ∀ s : unitInterval,
          s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
            |B ω s| < (1 / 4000 : ℝ)} :=
    avram_gaussianB_positive_long_centered_brownian_tube μB B hB
  have hMark : 0 < μJ {ω : ΩJ | τ 0 ω ≤ (1 / 500 : ℝ)} :=
    avram_jump6_A_actual_first_size2_mark_positive_before_any_time μJ τ Y hJ (1 / 500 : ℝ) (by norm_num)
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos (ne_of_gt hBrown) (ne_of_gt hMark)
