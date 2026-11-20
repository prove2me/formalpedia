-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_canonical_native_Brownian_gaussian_and_actual_firstmark_full_count_joint_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:36:12.836673+00:00
-- url     : https://prove2.me/submissions/d490bc22-a678-447c-b678-b1cd2499773c

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_AvramDividend_Classical_avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_firstmark_positive_time_precount_good_any_short_clock
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
      ({ωB : ℝ≥0 → ℝ |
        ∀ s : unitInterval,
          s ≤ (⟨(17 / 16000 : ℝ),
            by constructor <;> norm_num⟩ : unitInterval) →
            |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
              ProbabilityTheory.brownian 0 ωB| < (1 / 4000 : ℝ) ∧
            |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
              ProbabilityTheory.brownian 0 ωB + 2 * (s : ℝ)| <
              (1 / 400 : ℝ)} ×ˢ
       ({j : ΩJ |
          0 < τ 0 j ∧
          (∀ s : ℝ≥0, (s : ℝ) < arrival τ 0 j →
            jumpCount (fun n => arrival τ n j) (s : ℝ) = 0) ∧
          jumpCount (fun n => arrival τ n j) (arrival τ 0 j) = 1} ∩
        {j : ΩJ | τ 0 j ≤ (17 / 16000 : ℝ)})) := by
  haveI : IsProbabilityMeasure μJ := hJ.indep.isProbabilityMeasure
  have hBrown : 0 < gaussianLimit
      {ωB : ℝ≥0 → ℝ |
        ∀ s : unitInterval,
          s ≤ (⟨(17 / 16000 : ℝ),
            by constructor <;> norm_num⟩ : unitInterval) →
            |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
              ProbabilityTheory.brownian 0 ωB| < (1 / 4000 : ℝ) ∧
            |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
              ProbabilityTheory.brownian 0 ωB + 2 * (s : ℝ)| <
              (1 / 400 : ℝ)} :=
    avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
  have hMark : 0 < μJ (
      {j : ΩJ |
        0 < τ 0 j ∧
        (∀ s : ℝ≥0, (s : ℝ) < arrival τ 0 j →
          jumpCount (fun n => arrival τ n j) (s : ℝ) = 0) ∧
        jumpCount (fun n => arrival τ n j) (arrival τ 0 j) = 1} ∩
      {j : ΩJ | τ 0 j ≤ (17 / 16000 : ℝ)}) :=
    avram_jump6_A_original_firstmark_positive_time_precount_good_any_short_clock
      μJ τ Y hJ (17 / 16000 : ℝ) (by norm_num)
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos (ne_of_gt hBrown) (ne_of_gt hMark)
