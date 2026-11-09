-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin13_original_finite_activity_void_annulus_truncated_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:22:27.807213+00:00
-- url     : https://prove2.me/submissions/1ab9492d-a936-4d6c-a7d7-6e17c27a12be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m) (T : ℝ≥0) (ω : Ω)
    (hVoid :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioc (-(1 / ((n : ℝ) + 1)))
          (-(1 / ((m : ℝ) + 1)))) = 0) :
    |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
       avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
      (T : ℝ) * ((1 / ((n : ℝ) + 1)) *
        (X.ν (Iio (0 : ℝ))).toReal) := by
  have hSmall :=
    avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
      X hFinite n m hnm T ω hVoid
  have hIdentity :
      avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω =
      -(avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) := by
    unfold avram_p4_h_gaussian_intrinsic_truncated_residual
    ring
  rw [hIdentity, abs_neg]
  exact hSmall
