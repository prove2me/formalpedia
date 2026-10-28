-- Prove2me | solution 1 for AvramDividend.Classical.chat04_deterministic_horizon_scale_l2_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:02:16.10529+00:00
-- url     : https://prove2.me/submissions/9a72e919-3239-446e-ab71-f08bb93f80e7

import Theorems.Thm_AvramDividend_Classical_chat03_fixed_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- The deterministic-time q-scale square reward obeys a time-uniform
second-moment estimate on every bounded observation interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t : ℝ≥0) (htN : t ≤ N) :
    Integrable (fun ω =>
      (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (t : ℝ))) *
      W (x + X.X t ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let T : Ω → ℝ≥0 := fun _ => t
  let Z : Ω → ℝ := fun ω => X.X t ω
  have hZmeas : Measurable Z := by
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hWmeas : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hPayMeas : Measurable (fun ω =>
      (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2) := by
    have hw : Measurable (fun ω => W (x + Z ω)) :=
      hWmeas.comp (measurable_const.add hZmeas)
    have he : Measurable (fun _ : Ω => Real.exp (-(q * (t : ℝ)))) := measurable_const
    simpa only [T, Pi.mul_apply] using (he.mul hw).pow_const 2
  have hMomentInt : Integrable
      (fun ω => Real.exp (2 * θ * Z ω -
        (T ω : ℝ) * X.ψ (2 * θ))) P := by
    simpa only [T, Z] using
      (levy_compensated_exponential_integrable X t (2 * θ)
        (mul_nonneg (by norm_num) hθ))
  have hMomentOne :
      (∫ ω, Real.exp (2 * θ * Z ω -
        (T ω : ℝ) * X.ψ (2 * θ)) ∂P) = 1 := by
    simpa only [T, Z] using
      (levy_compensated_exponential_expectation_one
        X t (2 * θ) (mul_nonneg (by norm_num) hθ))
  have hBound : ∀ ω, T ω ≤ N := fun _ => htN
  simpa only [T, Z] using
    (chat03_fixed_horizon_scale_l2_bound
      X q hq W hW θ x hθ hψ N T Z hBound
      hPayMeas.aestronglyMeasurable hMomentInt hMomentOne)
