-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_canonical_actual_first_negative2_ruin_tube_concrete_joint_path_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:21:08.116113+00:00
-- url     : https://prove2.me/submissions/3306ac22-bf72-40f2-a5de-9827bec6b898

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_canonical_native_Brownian_gaussian_and_actual_firstmark_full_count_joint_positive
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
    ∃ (ωB : ℝ≥0 → ℝ) (ωJ : ΩJ),
      (∀ s : unitInterval,
        s ≤ (⟨(17 / 16000 : ℝ),
          by constructor <;> norm_num⟩ : unitInterval) →
          |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
            ProbabilityTheory.brownian 0 ωB| < (1 / 4000 : ℝ) ∧
          |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
            ProbabilityTheory.brownian 0 ωB +
            2 * (s : ℝ)| < (1 / 400 : ℝ)) ∧
      0 < τ 0 ωJ ∧
      (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ωJ →
        jumpCount (fun n => arrival τ n ωJ) (t : ℝ) = 0) ∧
      jumpCount (fun n => arrival τ n ωJ) (arrival τ 0 ωJ) = 1 ∧
      τ 0 ωJ ≤ (17 / 16000 : ℝ) := by
  have hPos :=
    avram_jump6_A_canonical_native_Brownian_gaussian_and_actual_firstmark_full_count_joint_positive
      μJ τ Y hJ
  obtain ⟨⟨ωB, ωJ⟩, hmem⟩ :=
    nonempty_of_measure_ne_zero (ne_of_gt hPos)
  rcases Set.mem_prod.mp hmem with ⟨hBrown, hJump⟩
  rcases hJump with ⟨hGood, hShort⟩
  exact ⟨ωB, ωJ, hBrown, hGood.1, hGood.2.1, hGood.2.2, hShort⟩
