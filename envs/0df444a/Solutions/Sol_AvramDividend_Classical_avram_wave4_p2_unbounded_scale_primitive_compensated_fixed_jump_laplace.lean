-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_compensated_fixed_jump_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:16:04.772072+00:00
-- url     : https://prove2.me/submissions/beb984d9-adb2-487f-85cb-a69ff0b03e92

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_shifted_laplace_transform
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_shifted_laplace_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- True compensated primitive single-jump Laplace transform without boundary defect. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x y) =
      (Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) *
        ((X.ψ θ - q)⁻¹ / θ) := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let k : ℝ := y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y
  let L : ℝ := (X.ψ θ - q)⁻¹
  have hWlap := hW.2.2.2.2 θ hθ.le hqθ
  have hUlap := positive_laplace_interval_primitive_real W θ hθ hWlap.1
  have hUshift : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * U (x+y))
      (Ioi (0 : ℝ)) volume :=
    avram_wave4_p2_source_scale_primitive_shifted_laplace_integrable
      X q W hW θ y hθ hqθ hy
  have hUbase : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * U x)
      (Ioi (0 : ℝ)) volume := hUlap.1
  have hD : deriv U = W :=
    avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
      X hnbv q hq W hW
  have hDeriv : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * deriv U x) (Ioi (0 : ℝ)) volume := by
    simpa only [hD] using hWlap.1
  have hInc : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * (U (x+y) - U x))
      (Ioi (0 : ℝ)) volume := by
    have hfun : (fun x : ℝ => Real.exp (-(θ*x)) * (U (x+y) - U x)) =
        (fun x : ℝ => Real.exp (-(θ*x)) * U (x+y) -
          Real.exp (-(θ*x)) * U x) := by
      funext x
      ring
    rw [hfun]
    exact hUshift.sub hUbase
  have hComp : IntegrableOn
      (fun x : ℝ => k * (Real.exp (-(θ*x)) * deriv U x))
      (Ioi (0 : ℝ)) volume := hDeriv.const_mul k
  have hRewrite :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        SpectrallyNegativeLevy.generatorIntegrand U x y) =
      ∫ x in Ioi (0 : ℝ),
        (Real.exp (-(θ*x)) * (U (x+y) - U x)) -
          k * (Real.exp (-(θ*x)) * deriv U x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp [k, SpectrallyNegativeLevy.generatorIntegrand]
    simp only [Pi.one_def]
    ring
  change (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
    SpectrallyNegativeLevy.generatorIntegrand U x y) = _
  rw [hRewrite, integral_sub hInc hComp, MeasureTheory.integral_const_mul]
  have hShift :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * U (x+y)) =
        Real.exp (θ*y) * (L/θ) := by
    simpa only [U, L] using
      (avram_wave4_p2_source_scale_primitive_shifted_laplace_transform
        X q W hW θ y hθ hqθ hy)
  have hBase :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * U x) = L/θ := by
    rw [hUlap.2, hWlap.2]
  have hDlap :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * deriv U x) = L := by
    simpa only [hD, L] using hWlap.2
  have hIncIntegral :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * (U (x+y) - U x)) =
        (Real.exp (θ*y) - 1) * (L/θ) := by
    have hx :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * (U (x+y) - U x)) =
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * U (x+y)) -
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * U x) := by
      convert integral_sub hUshift hUbase using 1
      · apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring
    rw [hx, hShift, hBase]
    ring
  rw [hIncIntegral, hDlap]
  dsimp [L, k]
  field_simp [ne_of_gt hθ]
