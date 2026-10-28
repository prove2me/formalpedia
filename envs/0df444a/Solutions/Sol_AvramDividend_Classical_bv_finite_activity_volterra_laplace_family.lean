-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_volterra_laplace_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:21:22.329204+00:00
-- url     : https://prove2.me/submissions/6ab153bb-8148-4027-acce-e26e87ac61b4

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_weighted_integrable_finite_activity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_laplace_finite_activity
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_finite_jump_rearrangement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Exponential integrability and coincident Laplace transforms for the
    finite-activity scale renewal equation at sufficiently large exponents. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * X.drift * W x)
        (Ioi (0 : ℝ)) volume ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
        ∫ z in (0 : ℝ)..x,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)))
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * X.drift * W x) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
        ∫ z in (0 : ℝ)..x,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)) := by
  let J : ℝ → ℝ := fun z => ∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν
  let PW : ℝ → ℝ := fun x => ∫ z in (0 : ℝ)..x, W z
  let PJ : ℝ → ℝ := fun x => ∫ z in (0 : ℝ)..x, J z
  let f : ℝ → ℝ := fun x => X.drift * W x
  let g : ℝ → ℝ := fun x => 1 + (q + (X.ν (Iio (0 : ℝ))).toReal) * PW x - PJ x
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
  refine ⟨b, ?_⟩
  intro θ hθ
  simpa only [f, g, PW, PJ, J, neg_mul, mul_assoc] using hlap θ hθ
