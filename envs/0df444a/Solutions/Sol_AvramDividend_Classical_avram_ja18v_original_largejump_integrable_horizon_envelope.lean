-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18v_original_largejump_integrable_horizon_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:56:03.027744+00:00
-- url     : https://prove2.me/submissions/00e7e0aa-d392-4b21-87c3-7e8f0fc70147

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18u_original_largejump_sum_antitone
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_largejump_sum_pathwise_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_largejump_sum_L1_of_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original negative large jumps are dominated by their L1 terminal magnitude. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    Integrable
      (fun ω => ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X (n : ℝ≥0) ω‖) P ∧
    (∀ ω : Ω, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
      ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ ≤
      ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X (n : ℝ≥0) ω‖) := by
  constructor
  · exact (avram_ja18_original_largejump_sum_L1_of_standing
      X hX hFinite (n : ℝ≥0)).norm
  · intro ω t ht
    have hmon :=
      avram_ja18u_original_largejump_sum_antitone
        X ω t (n : ℝ≥0) ht
    have hnegT :=
      avram_ja18g_original_largejump_sum_pathwise_nonpos X t ω
    have hnegN :=
      avram_ja18g_original_largejump_sum_pathwise_nonpos
        X (n : ℝ≥0) ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos hnegT, abs_of_nonpos hnegN]
    linarith
