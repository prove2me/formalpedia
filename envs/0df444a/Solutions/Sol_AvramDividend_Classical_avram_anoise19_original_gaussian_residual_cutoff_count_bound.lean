-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise19_original_gaussian_residual_cutoff_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:23:19.368244+00:00
-- url     : https://prove2.me/submissions/ee31382e-5740-4320-be91-9a246888f1b4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original Gaussian cutoff bound from finite physical count and compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m) (T : ℝ≥0) (ω : Ω)
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    let N : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    let A : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
      (1 / ((n : ℝ) + 1)) * (N.toReal + A) := by
  intro N A
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  let S : Set ℝ := Ioc (-ε) (-(1 / ((m : ℝ) + 1)))
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ S
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hUpper : -(1 / ((m : ℝ) + 1)) < 0 :=
    neg_lt_zero.mpr (by positivity)
  have hSnegative : S ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact lt_of_le_of_lt hz.2 hUpper
  have hSsmall : S ⊆ Ioo (-ε) 0 := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hUpper⟩
  have hBsub : B ⊆ Ioc 0 T ×ˢ Iio (0 : ℝ) :=
    Set.prod_mono (Subset.rfl) hSnegative
  have hMeasB : MeasurableSet B :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hCount : NX B ≤ N := by
    change NX B ≤ NX (Ioc 0 T ×ˢ Iio (0 : ℝ))
    exact measure_mono hBsub
  have hBfinite : NX B ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hCount hNfin)
  have hRateFinite : (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hFinite
  have hMassFinite : ENNReal.ofReal ε * NX B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfinite
  have hAbsWithin (p : ℝ≥0 × ℝ) (hp : p ∈ B) : |p.2| ≤ ε := by
    have hz : p.2 ∈ S := hp.2
    have hzNeg : p.2 < 0 := hSnegative hz
    rw [abs_of_neg hzNeg]
    linarith [hz.1]
  have hNorm :
      |∫ p in B, p.2 ∂NX| ≤
        (∫⁻ p in B, ENNReal.ofReal |p.2| ∂NX).toReal := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_lintegral_norm
        (μ := NX.restrict B) (fun p : ℝ≥0 × ℝ => p.2))
  have hLinBound :
      (∫⁻ p in B, ENNReal.ofReal |p.2| ∂NX) ≤
        ENNReal.ofReal ε * NX B := by
    calc
      (∫⁻ p in B, ENNReal.ofReal |p.2| ∂NX) ≤
          ∫⁻ p in B, ENNReal.ofReal ε ∂NX := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hMeasB] with p hp
        exact ENNReal.ofReal_le_ofReal (hAbsWithin p hp)
      _ = ENNReal.ofReal ε * NX B := by
        simp [lintegral_const, B]
  have hCountReal : (NX B).toReal ≤ N.toReal :=
    ENNReal.toReal_mono (ne_of_lt hNfin) hCount
  have hPathBound :
      |∫ p in B, p.2 ∂NX| ≤ ε * N.toReal := by
    calc
      |∫ p in B, p.2 ∂NX| ≤
          (∫⁻ p in B, ENNReal.ofReal |p.2| ∂NX).toReal := hNorm
      _ ≤ (ENNReal.ofReal ε * NX B).toReal :=
        ENNReal.toReal_mono hMassFinite hLinBound
      _ = ε * (NX B).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hε)]
      _ ≤ ε * N.toReal :=
        mul_le_mul_of_nonneg_left hCountReal (le_of_lt hε)
  have hNuBound :
      |∫ z in S, z ∂X.ν| ≤ ε * (X.ν (Iio (0 : ℝ))).toReal :=
    avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le
      X hFinite ε (le_of_lt hε) S measurableSet_Ioc hSsmall
  have hSource :
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω =
      (∫ p in B, p.2 ∂NX) - (T : ℝ) * (∫ z in S, z ∂X.ν) := by
    calc
      _ = avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω :=
        avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
          X n m T ω
      _ = (∫ p in B, p.2 ∂NX) -
          (T : ℝ) * (∫ z in S, z ∂X.ν) := by
        simpa only [B, NX, S, ε] using
          avram_p4_h_gaussian_original_smalljump_cutoff_strip
            X n m hnm T ω
  have hTnonneg : 0 ≤ (T : ℝ) := by exact_mod_cast T.property
  have hNuTimes :
      |(T : ℝ) * (∫ z in S, z ∂X.ν)| ≤
        (T : ℝ) * (ε * (X.ν (Iio (0 : ℝ))).toReal) := by
    rw [abs_mul, abs_of_nonneg hTnonneg]
    exact mul_le_mul_of_nonneg_left hNuBound hTnonneg
  change |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
    ε * (N.toReal + A)
  calc
    |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| =
        |(∫ p in B, p.2 ∂NX) -
          (T : ℝ) * (∫ z in S, z ∂X.ν)| := by
      rw [abs_sub_comm, hSource]
    _ ≤ |∫ p in B, p.2 ∂NX| +
        |(T : ℝ) * (∫ z in S, z ∂X.ν)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (∫ p in B, p.2 ∂NX)
          (-((T : ℝ) * (∫ z in S, z ∂X.ν))))
    _ ≤ ε * N.toReal +
        (T : ℝ) * (ε * (X.ν (Iio (0 : ℝ))).toReal) :=
      add_le_add hPathBound hNuTimes
    _ = ε * (N.toReal + A) := by
      dsimp [A]
      rw [ENNReal.toReal_mul]
      simp only [ENNReal.coe_toReal]
      ring