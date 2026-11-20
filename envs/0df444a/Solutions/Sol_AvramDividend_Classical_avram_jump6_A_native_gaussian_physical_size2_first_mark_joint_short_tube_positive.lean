-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_native_gaussian_physical_size2_first_mark_joint_short_tube_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:45:42.212477+00:00
-- url     : https://prove2.me/submissions/6ef4861f-567b-4990-9119-4eb8322d3f5e

import Mathlib
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_AvramDividend_Classical_avram_gbWill_20261117_native_centered_short_event_positive
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_mark_positive_before_any_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    [IsProbabilityMeasure gaussianLimit]
    {ΩJ : Type*} [MeasurableSpace ΩJ]
    (μJ : Measure ΩJ) (τ Y : ℕ → ΩJ → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μJ) :
    0 < (gaussianLimit.prod μJ)
      ({ωB : ℝ≥0 → ℝ | ∀ s : unitInterval,
          s ≤ (⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
            |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
                ProbabilityTheory.brownian 0 ωB| < (1 / 4000 : ℝ)} ×ˢ
        {ωJ : ΩJ | τ 0 ωJ ≤ (1 / 1000 : ℝ)}) := by
  letI : IsProbabilityMeasure μJ := hJ.indep.isProbabilityMeasure
  have hBrown :
      0 < gaussianLimit {ω : ℝ≥0 → ℝ |
        ∀ s : unitInterval,
          s ≤ (⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
          |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
            ProbabilityTheory.brownian 0 ω| < (1 / 4000 : ℝ)} :=
    avram_gbWill_20261117_native_centered_short_event_positive
  have hMark : 0 < μJ {ω : ΩJ | τ 0 ω ≤ (1 / 1000 : ℝ)} :=
    avram_jump6_A_actual_first_size2_mark_positive_before_any_time
      μJ τ Y hJ (1 / 1000 : ℝ) (by norm_num)
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos (ne_of_gt hBrown) (ne_of_gt hMark)
