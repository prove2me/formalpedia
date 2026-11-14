-- Prove2me | solution 4 for AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:57:52.8252+00:00
-- url     : https://prove2.me/submissions/ed9754d2-050b-451e-8034-ef801de88c5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_original_zero_cutoff_gaussian_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The true zero-cutoff L2 premise and actual compensated cutoff imply every residual L2. -/
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
  have hG := avram_ja18i_original_zero_cutoff_gaussian_square_integrable
    X hX hFinite t
  have hJ : Integrable (fun ω =>
      (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2) P := by
    simpa only [neg_sq] using
      (avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
        X hFinite n t)
  apply avram_ja19_square_integrable_of_ae_sum_components
    (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
    (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω)
    (fun ω => -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
    hf hG hJ
  filter_upwards [] with ω
  simpa only [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff,
    add_zero, sub_eq_add_neg] using
    (avram_ja21_original_cutoff_residual_gaussian_core_split X n t ω)
