-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_brownian_tube_and_early_size2_mark_positive_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:42:45.772235+00:00
-- url     : https://prove2.me/submissions/3c65147c-e8ce-4c31-ab9c-3d0f97dd7544

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_positive_long_centered_brownian_tube
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_rateone_first_size2_mark_before_tenth_positive
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
       {ω : ΩJ | τ 0 ω ≤ (1 / 10 : ℝ)}) := by
  letI : IsProbabilityMeasure μJ := hJ.indep.isProbabilityMeasure
  have hBrown : 0 < μB
      {ω : ΩB | ∀ s : unitInterval,
          s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
            |B ω s| < (1 / 4000 : ℝ)} :=
    avram_gaussianB_positive_long_centered_brownian_tube μB B hB
  have hMark : 0 < μJ {ω : ΩJ | τ 0 ω ≤ (1 / 10 : ℝ)} :=
    avram_jump6_A_actual_rateone_first_size2_mark_before_tenth_positive μJ τ Y hJ
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos (ne_of_gt hBrown) (ne_of_gt hMark)
