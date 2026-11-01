-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_generator_residual_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:48:54.950138+00:00
-- url     : https://prove2.me/submissions/c8fee627-bcda-45e5-ba78-a8589904b8ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_jump_laplace_of_product_fubini
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Pure-jump source primitive generator residual has Laplace transform 1/θ. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) *
      (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
        q * (∫ t in (0 : ℝ)..x, W t))) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
      (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
        q * (∫ t in (0 : ℝ)..x, W t))) = 1 / θ := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let K : ℝ → ℝ := fun x => ∫ y in Iio (0 : ℝ),
    SpectrallyNegativeLevy.generatorIntegrand U x y ∂X.ν
  let J : ℝ := ∫ y in Iio (0 : ℝ),
    Real.exp (θ*y) - 1 -
      θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν
  let A : ℝ := (X.ψ θ - q)⁻¹
  have hWlap := hW.2.2.2.2 θ hθ.le hqθ
  have hUlap := positive_laplace_interval_primitive_real W θ hθ hWlap.1
  have hD : deriv U = W :=
    avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
      X hnbv q hq W hW
  have hDint : IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * deriv U x)
      (Ioi (0 : ℝ)) volume := by simpa only [hD] using hWlap.1
  have hUint : IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * U x)
      (Ioi (0 : ℝ)) volume := hUlap.1
  have hprod :=
    avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
      X hX hnbv q hq W hW θ hθ hqθ
  have hJint : IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * K x)
      (Ioi (0 : ℝ)) volume :=
    bv_weighted_jump_integrable_of_product_integrable X θ U hprod
  have hDconst : IntegrableOn
      (fun x : ℝ => X.c * (Real.exp (-(θ*x)) * deriv U x))
      (Ioi (0 : ℝ)) volume := hDint.const_mul X.c
  have hUq : IntegrableOn
      (fun x : ℝ => q * (Real.exp (-(θ*x)) * U x))
      (Ioi (0 : ℝ)) volume := hUint.const_mul q
  have hgen (x : ℝ) : X.generator U x = X.c * deriv U x + K x := by
    unfold SpectrallyNegativeLevy.generator
    simp [hσ, K]
  have hp (x : ℝ) :
      Real.exp (-(θ*x)) * (X.generator U x - q * U x) =
        X.c * (Real.exp (-(θ*x)) * deriv U x) +
          Real.exp (-(θ*x)) * K x -
          q * (Real.exp (-(θ*x)) * U x) := by
    rw [hgen]
    ring
  have hResInt : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * (X.generator U x - q * U x))
      (Ioi (0 : ℝ)) volume := by
    have heq : (fun x : ℝ => Real.exp (-(θ*x)) * (X.generator U x - q * U x)) =
      (fun x : ℝ => X.c * (Real.exp (-(θ*x)) * deriv U x) +
        Real.exp (-(θ*x)) * K x - q * (Real.exp (-(θ*x)) * U x)) := by
      funext x
      exact hp x
    rw [heq]
    exact (hDconst.add hJint).sub hUq
  have hResEq :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        (X.generator U x - q * U x)) =
      X.c * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * deriv U x) +
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * K x) -
      q * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * U x) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
        X.c * (Real.exp (-(θ*x)) * deriv U x) +
          Real.exp (-(θ*x)) * K x -
          q * (Real.exp (-(θ*x)) * U x) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            exact hp x
      _ = _ := by
        have hsub := MeasureTheory.integral_sub (hDconst.add hJint) hUq
        have hadd := MeasureTheory.integral_add hDconst hJint
        have hadd' :
            (∫ x in Ioi (0 : ℝ),
              ((fun x => X.c * (Real.exp (-(θ*x)) * deriv U x)) +
                (fun x => Real.exp (-(θ*x)) * K x)) x) =
            (∫ x in Ioi (0 : ℝ),
              X.c * (Real.exp (-(θ*x)) * deriv U x)) +
              (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * K x) := by
          simpa only [Pi.add_apply] using hadd
        have h := hsub.trans (by
          rw [hadd', MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul])
        simpa only [Pi.sub_apply, Pi.add_apply] using h
  have hJump :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * K x) = J * (A/θ) := by
    simpa only [K, J, A] using
      avram_wave4_p2_unbounded_scale_primitive_jump_laplace_of_product_fubini
        X hX hnbv q hq W hW θ hθ hqθ
  have hDlap :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * deriv U x) = A := by
    simpa only [hD, A] using hWlap.2
  have hUlapEq :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * U x) = A/θ := by
    rw [hUlap.2, hWlap.2]
  have hψ : X.ψ θ = X.c * θ + J := by
    simp only [SpectrallyNegativeLevy.ψ, laplaceExponent, hσ,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div, add_zero, J]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    change Real.exp (θ*y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y =
      Real.exp (θ*y) - 1 -
      θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
    ring
  change IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) *
    (X.generator U x - q * U x)) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
      (X.generator U x - q * U x)) = 1 / θ
  refine ⟨hResInt, ?_⟩
  rw [hResEq, hDlap, hJump, hUlapEq]
  have hA : X.ψ θ - q ≠ 0 := ne_of_gt (sub_pos.mpr hqθ)
  dsimp [A] at *
  rw [hψ] at *
  field_simp [hA, ne_of_gt hθ]
