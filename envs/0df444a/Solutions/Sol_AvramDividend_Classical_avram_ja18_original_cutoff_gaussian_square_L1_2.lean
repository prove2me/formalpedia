-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:11:04.727624+00:00
-- url     : https://prove2.me/submissions/048d495c-a3f5-467e-8738-4e1e2c8a0bb0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_fixed_gaussian_core_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original cutoff residual L2 follows from its physical core and small-band L2. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P := by
  intro n t
  have hf : AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hG := (avram_ja21_original_fixed_gaussian_core_second_moment
    X hX hFinite t).1
  have hJ : Integrable (fun ω =>
      (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2) P := by
    simpa only [neg_sq] using
      (avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
        X hFinite n t)
  apply avram_ja19_square_integrable_of_ae_sum_components
    (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
    (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω)
    (fun ω => -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
    hf hG hJ
  filter_upwards [] with ω
  simpa only [sub_eq_add_neg] using
    (avram_ja21_original_cutoff_residual_gaussian_core_split X n t ω)
