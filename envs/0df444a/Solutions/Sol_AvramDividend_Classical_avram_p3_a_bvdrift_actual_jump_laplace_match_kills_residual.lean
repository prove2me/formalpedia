-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_laplace_match_kills_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:36:36.849844+00:00
-- url     : https://prove2.me/submissions/b19a488a-4d39-4a46-9abc-5ecbd1861ae1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
/-- Genuine jump Laplace identity kills the original BV residual without raw first moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ)
    (hJInt : Integrable (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal))) P)
    (hXInt : Integrable (fun ω : Ω =>
      Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift))) P)
    (hJLap : (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
      Real.exp (-(T : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
    ∀ᵐ ω ∂P, ((T : ℝ) * X.drift - X.X T ω) - (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal = 0 := by
  have hθ0 : 0 ≤ θ := by linarith only [hθ]
  have hdef := bv_exponent_negative_jump_deficit_exact X hBV θ hθ
  have hXlap := (X.laplace T θ hθ0).2
  have hXMean :
      (∫ ω : Ω, Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift)) ∂P) =
        Real.exp ((T : ℝ) * (X.ψ θ - θ * X.drift)) := by
    calc
      (∫ ω : Ω, Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift)) ∂P) =
        ∫ ω : Ω, Real.exp (-(θ * (T : ℝ) * X.drift)) *
          Real.exp (θ * X.X T ω) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [← Real.exp_add]
          congr 1
          ring
      _ = Real.exp (-(θ * (T : ℝ) * X.drift)) *
            (∫ ω : Ω, Real.exp (θ * X.X T ω) ∂P) :=
        integral_const_mul _ _
      _ = Real.exp ((T : ℝ) * (X.ψ θ - θ * X.drift)) := by
        rw [hXlap, ← Real.exp_add]
        congr 1
        change -(θ * (T : ℝ) * X.drift) + (T : ℝ) * X.ψ θ =
          (T : ℝ) * (X.ψ θ - θ * X.drift)
        ring
  have hEqual :
      (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        (∫ ω : Ω,
          Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift)) ∂P) := by
    rw [hJLap, hXMean, ← hdef]
    congr 1
    ring
  have hBound : ∀ᵐ ω ∂P,
      X.X T ω ≤ (T : ℝ) * X.drift - (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by
    filter_upwards
      [avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
        X hBV,
       avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
        X hBV] with ω hDrift hEncoding
    have hb := hDrift 0 T (by positivity)
    have he := hEncoding T
    simp only [NNReal.coe_zero, zero_sub, sub_zero] at hb
    rw [X.X_zero ω] at hb
    simp only [sub_zero] at hb
    linarith only [hb, he]
  have hDiffNonneg : 0 ≤ᵐ[P] (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) -
        Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift))) := by
    filter_upwards [hBound] with ω hω
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left
      (show X.X T ω - (T : ℝ) * X.drift ≤ -(∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal by
        linarith only [hω]) hθ0
    nlinarith only [hm]
  have hDiffInt : Integrable (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) -
        Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift))) P :=
    hJInt.sub hXInt
  have hDiffMean :
      (∫ ω : Ω,
        Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) -
          Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift)) ∂P) = 0 := by
    rw [integral_sub hJInt hXInt]
    linarith only [hEqual]
  have hDiffZero := (integral_eq_zero_iff_of_nonneg_ae hDiffNonneg hDiffInt).mp hDiffMean
  filter_upwards [hDiffZero] with ω hω
  have hExpEq :
      Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) =
        Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift)) :=
    sub_eq_zero.mp hω
  have hArg := Real.exp_injective hExpEq
  have hθne : θ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hθ)
  have hMul :
      θ * (((T : ℝ) * X.drift - X.X T ω) - (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) = 0 := by
    nlinarith only [hArg]
  exact (mul_eq_zero.mp hMul).resolve_left hθne
