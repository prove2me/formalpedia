-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_zero_cutoff_fixed_time_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T20:40:21.428045+00:00
-- url     : https://prove2.me/submissions/a97f81ce-e9ea-47ce-bdde-95b1ed8f1532

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_largejump_sum_L1_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The zero cutoff has no compensated small marks; original X_t, its
deterministic drift and the original large-jump sum are individually L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  have hXint : Integrable (X.X t) P :=
    avram_ja18_standing_X_integrable_fixedtime X hX t
  have hJint : Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) P :=
    avram_ja18_original_largejump_sum_L1_of_standing X hX hFinite t
  have hMain : Integrable (fun ω =>
      X.X t ω - (t : ℝ) * X.c -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) P :=
    (hXint.sub (integrable_const ((t : ℝ) * X.c))).sub hJint
  have hEq :
      (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) =
      (fun ω => X.X t ω - (t : ℝ) * X.c -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) := by
    funext ω
    simp [avram_p4_h_gaussian_intrinsic_truncated_residual,
      avram_p4_h_gaussian_intrinsic_small_band_compensated]
  rw [hEq]
  exact hMain
