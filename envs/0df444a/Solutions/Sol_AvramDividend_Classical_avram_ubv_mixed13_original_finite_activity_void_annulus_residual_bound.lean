-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:19:09.648683+00:00
-- url     : https://prove2.me/submissions/25a25287-5376-4f16-a0bf-b8a465def9f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A physically empty small-jump annulus leaves only a quantitatively
bounded deterministic compensator in the original Gaussian residual. -/
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
    |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| ≤
      (T : ℝ) * ((1 / ((n : ℝ) + 1)) *
        (X.ν (Iio (0 : ℝ))).toReal) := by
  let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hSub : S ⊆ Ioo (-(1 / ((n : ℝ) + 1))) 0 := by
    intro z hz
    refine ⟨hz.1, lt_of_le_of_lt hz.2 ?_⟩
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hReal : |∫ z in S, z ∂X.ν| ≤
      (1 / ((n : ℝ) + 1)) * (X.ν (Iio (0 : ℝ))).toReal := by
    exact avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le
      X hFinite _ (by positivity) S measurableSet_Ioc hSub
  have hZero : (∫ p in (Ioc 0 T ×ˢ S), p.2 ∂NX) = 0 := by
    apply setIntegral_measure_zero
    exact hVoid
  have hStrip :=
    avram_p4_h_gaussian_original_smalljump_cutoff_strip X n m hnm T ω
  change
    avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω =
        (∫ p in (Ioc 0 T ×ˢ S), p.2 ∂NX) -
          (T : ℝ) * (∫ z in S, z ∂X.ν) at hStrip
  have hT : (0 : ℝ) ≤ (T : ℝ) := by positivity
  calc
    |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| =
        |(∫ p in (Ioc 0 T ×ˢ S), p.2 ∂NX) -
          (T : ℝ) * (∫ z in S, z ∂X.ν)| := congrArg abs hStrip
    _ = (T : ℝ) * |∫ z in S, z ∂X.ν| := by
      rw [hZero, zero_sub, abs_neg, abs_mul, abs_of_nonneg hT]
    _ ≤ (T : ℝ) * ((1 / ((n : ℝ) + 1)) *
          (X.ν (Iio (0 : ℝ))).toReal) :=
      mul_le_mul_of_nonneg_left hReal hT
