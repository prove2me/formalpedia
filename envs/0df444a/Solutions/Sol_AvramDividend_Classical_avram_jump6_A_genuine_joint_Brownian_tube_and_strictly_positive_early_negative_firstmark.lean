-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_genuine_joint_Brownian_tube_and_strictly_positive_early_negative_firstmark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:52:46.789725+00:00
-- url     : https://prove2.me/submissions/8966cfbd-0cad-4c36-bbee-349fd9926d73

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_positive_long_centered_brownian_tube
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_rateone_size2_first_mark_strictly_positive_and_early_event
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
       {ω : ΩJ | 0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)}) := by
  letI : IsProbabilityMeasure μJ := hJ.indep.isProbabilityMeasure
  have hBrown : 0 < μB
      {ω : ΩB | ∀ s : unitInterval,
          s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
            |B ω s| < (1 / 4000 : ℝ)} :=
    avram_gaussianB_positive_long_centered_brownian_tube μB B hB
  have hMark : 0 < μJ
      {ω : ΩJ | 0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)} :=
    avram_jump6_A_original_rateone_size2_first_mark_strictly_positive_and_early_event
      μJ τ Y hJ
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos (ne_of_gt hBrown) (ne_of_gt hMark)
