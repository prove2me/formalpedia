-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:56:19.361705+00:00
-- url     : https://prove2.me/submissions/d2d6fb30-1f3a-4192-a644-722bca6584ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_negative_band_integral_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every exact original Gaussian finite-cutoff residual is adapted to its own physical horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (T : ℝ≥0) :
    Measurable[𝓕 T] (fun ω : Ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) := by
  have hX : Measurable[𝓕 T] (X.X T) := X.adapted T
  have hBandNeg : ∀ z ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ≤ 0 := by
    intro z hz
    have hn : 0 ≤ (1 / ((n : ℝ) + 1)) := by positivity
    exact hz.2.trans (neg_nonpos.mpr hn)
  have hBand := avram_mix_gauss14_original_negative_band_integral_adapted
    X T (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) measurableSet_Ioc hBandNeg
  have hSmall : Measurable[𝓕 T] (fun ω =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) := by
    simpa only [avram_p4_h_gaussian_intrinsic_small_band_compensated] using
      hBand.sub_const ((T : ℝ) *
        (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
  have hLarge : Measurable[𝓕 T] (fun ω =>
      avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω) := by
    simpa only [avram_p4_h_gaussian_intrinsic_large_jump_sum] using
      avram_mix_gauss14_original_negative_band_integral_adapted
        X T (Iic (-1 : ℝ)) measurableSet_Iic
        (by intro z hz; exact hz.trans (by norm_num))
  have hRes : Measurable[𝓕 T] (fun ω =>
      X.X T ω - (T : ℝ) * X.c -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω) :=
    ((hX.sub_const ((T : ℝ) * X.c)).sub hSmall).sub hLarge
  simpa only [avram_p4_h_gaussian_intrinsic_truncated_residual] using hRes
