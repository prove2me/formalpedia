-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_scale_volterra_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:17:32.209481+00:00
-- url     : https://prove2.me/submissions/fe757c47-6d0c-41de-8754-d66fbb902f7b

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_weighted_integrable_finite_activity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_laplace_finite_activity
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_finite_jump_rearrangement
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The finite-activity BV renewal equation follows by equality of Laplace
    transforms, with continuity recovering equality at every positive state. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ x : ℝ, 0 < x →
      X.drift * W x =
        1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
          ∫ z in (0 : ℝ)..x,
            (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν) := by
  let J : ℝ → ℝ := fun z => ∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν
  let PW : ℝ → ℝ := fun x => ∫ z in (0 : ℝ)..x, W z
  let PJ : ℝ → ℝ := fun x => ∫ z in (0 : ℝ)..x, J z
  let f : ℝ → ℝ := fun x => X.drift * W x
  let g : ℝ → ℝ := fun x => 1 + (q + (X.ν (Iio (0 : ℝ))).toReal) * PW x - PJ x
  have hWcont : ContinuousOn W (Ioi (0 : ℝ)) := by
    intro x hx
    exact (scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx)).continuousWithinAt
  have hJcont : ContinuousOn J (Ici (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_nonnegative X hX q hq W hW hBV hFinite
  have hWInt (x : ℝ) (hx : 0 < x) : IntervalIntegrable W volume 0 x := scaleFunction_intervalIntegrable_nonnegative X q W hW 0 x (le_refl 0) (le_of_lt hx)
  have hJInt (x : ℝ) (hx : 0 < x) : IntervalIntegrable J volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    apply hJcont.mono
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le (le_of_lt hx)] using ht
    exact ht'.1
  have hPWcont : ContinuousOn PW (Ioi (0 : ℝ)) := by
    have hd := contDiffOn_one_const_add_intervalIntegral W 0 hWcont hWInt
    simpa [PW] using hd.continuousOn
  have hPJcont : ContinuousOn PJ (Ioi (0 : ℝ)) := by
    have hJcontpos : ContinuousOn J (Ioi (0 : ℝ)) :=
      hJcont.mono (Ioi_subset_Ici_self)
    have hd := contDiffOn_one_const_add_intervalIntegral J 0 hJcontpos hJInt
    simpa [PJ] using hd.continuousOn
  have hfcont : ContinuousOn f (Ioi (0 : ℝ)) := continuousOn_const.mul hWcont
  have hgcont : ContinuousOn g (Ioi (0 : ℝ)) := (continuousOn_const.add (continuousOn_const.mul hPWcont)).sub hPJcont
  obtain ⟨β, hβ, hβq⟩ := psi_eventually_gt_of_standing X hX q hq
  let b : ℝ := max 1 β
  have hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * f x)
        (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * g x)
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * f x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x := by
    intro θ hθb
    have hθ : 0 < θ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans (le_max_left 1 β) (le_of_lt hθb))
    have hθone : 1 ≤ θ := le_trans (le_max_left 1 β) (le_of_lt hθb)
    have hqθ : q < X.ψ θ := hβq θ (le_trans (le_max_right 1 β) (le_of_lt hθb))
    have hWweighted : IntegrableOn
        (fun x : ℝ => Real.exp (-(θ * x)) * W x) (Ioi 0) :=
      by simpa using scaleFunction_shiftedLaplace_integrable X q W hW θ 0 (le_of_lt hθ) hqθ (le_refl 0)
    have hJweighted : IntegrableOn
        (fun x : ℝ => Real.exp (-(θ * x)) * J x) (Ioi 0) := by
      exact scaleFunction_jump_convolution_weighted_integrable_finite_activity X q W hW θ (le_of_lt hθ) hqθ hFinite
    obtain ⟨hPWweighted, hLapPW⟩ := positive_laplace_interval_primitive_real W θ hθ hWweighted
    obtain ⟨hPJweighted, hLapPJ⟩ := positive_laplace_interval_primitive_real J θ hθ hJweighted
    obtain ⟨hconstweighted, hLapConst⟩ := positive_laplace_constant_reference θ hθ
    have hfweighted : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * f x) (Ioi 0) := by
      have hfun : (fun x : ℝ => Real.exp (-(θ * x)) * f x) =
          (fun x : ℝ => X.drift * (Real.exp (-(θ * x)) * W x)) := by
        funext x; dsimp [f]; ring
      rw [hfun]
      exact hWweighted.const_mul X.drift
    have hgweighted : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * g x) (Ioi 0) := by
      have hh := (hconstweighted.add (hPWweighted.const_mul
        (q + (X.ν (Iio (0 : ℝ))).toReal))).sub hPJweighted
      convert hh using 1
      funext x; dsimp [g]; ring
    refine ⟨(by simpa only [neg_mul] using hfweighted),
      (by simpa only [neg_mul] using hgweighted), ?_⟩
    have hWlap : (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) = (X.ψ θ - q)⁻¹ := by
      simpa only [add_zero, mul_zero, Real.exp_zero, one_mul] using
        scaleFunction_shifted_laplace_transform X q W hW θ 0 (le_of_lt hθ) hqθ (le_refl 0)
    have hJlap := scaleFunction_jump_convolution_laplace_finite_activity X q W hW θ (le_of_lt hθ) hqθ hFinite
    have hψ := bv_laplace_exponent_finite_jump_rearrangement X hBV θ hθone hFinite
    have hθne : θ ≠ 0 := ne_of_gt hθ
    have hDne : X.ψ θ - q ≠ 0 := ne_of_gt (sub_pos.mpr hqθ)
    have hrel : X.ψ θ - q + q + (X.ν (Iio (0 : ℝ))).toReal -
      (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) = X.drift * θ := by
      rw [hψ]; ring
    have hflap :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x) =
          X.drift * (X.ψ θ - q)⁻¹ := by
      calc
        _ = ∫ x in Ioi (0 : ℝ), X.drift * (Real.exp (-(θ * x)) * W x) := by
          congr 1; funext x; dsimp [f]; ring
        _ = X.drift * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) := by
          rw [MeasureTheory.integral_const_mul]
        _ = _ := by rw [hWlap]
    have hglap :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * g x) =
          1 / θ + (q + (X.ν (Iio (0 : ℝ))).toReal) *
            ((X.ψ θ - q)⁻¹ / θ) -
            ((∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) *
              (X.ψ θ - q)⁻¹ / θ) := by
      have hrew : (fun x : ℝ => Real.exp (-(θ * x)) * g x) =
          (fun x : ℝ => Real.exp (-(θ * x)) + (q + (X.ν (Iio (0 : ℝ))).toReal) *
            (Real.exp (-(θ * x)) * PW x) - Real.exp (-(θ * x)) * PJ x) := by
        funext x; dsimp [g]; ring
      rw [hrew]
      have hs := MeasureTheory.integral_sub
        (hconstweighted.add (hPWweighted.const_mul
          (q + (X.ν (Iio (0 : ℝ))).toReal))) hPJweighted
      simp only [Pi.add_apply, Pi.sub_apply] at hs
      rw [MeasureTheory.integral_add hconstweighted
        (hPWweighted.const_mul (q + (X.ν (Iio (0 : ℝ))).toReal))] at hs
      rw [hs]
      rw [MeasureTheory.integral_const_mul, hLapConst, hLapPW, hLapPJ, hWlap, hJlap]
    simp only [neg_mul]
    rw [hflap, hglap]
    field_simp
    nlinarith [hrel]
  have heq := continuousOn_Ioi_eq_of_laplace_eq_signed f g b hfcont hgcont hlap
  intro x hx
  exact heq x hx
