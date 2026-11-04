-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_correction_dominated_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:07:11.742863+00:00
-- url     : https://prove2.me/submissions/d6e8699a-9038-4f65-ba02-0f906ea97920

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Localised original-source Gaussian Hessian corrections pass through
time integration by dominated convergence on a true stopped interval.
The time-state approximations and their a.e. convergence remain explicit;
no global C2 bound, endpoint occupation claim or Brownian input is used. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (μ : Measure ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω)
    (hFinite : μ (Iio (τ ω)) < ⊤)
    (Vn : ℕ → ℝ≥0 → ℝ) (V : ℝ≥0 → ℝ)
    (hIn : ∀ n, ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))), Vn n s ∈ Icc a b)
    (hMeas : ∀ n, AEStronglyMeasurable (fun s : ℝ≥0 =>
      Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s)))
      (μ.restrict (Iio (τ ω))))
    (hConv : ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      Tendsto (fun n => Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s)))
        atTop (nhds (Real.exp (-(q * (s : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (V s))))) :
    Tendsto (fun n => ∫ (s : ℝ≥0), Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s))
      ∂(μ.restrict (Iio (τ ω)))) atTop
      (nhds (∫ (s : ℝ≥0), Real.exp (-(q * (s : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (V s))
        ∂(μ.restrict (Iio (τ ω))))) := by
  obtain ⟨K, hK, hBound⟩ :=
    avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
      X q hq C w hwC2 a b hBand
  haveI : IsFiniteMeasure (μ.restrict (Iio (τ ω))) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt hFinite)
  have hKInt : Integrable (fun _ : ℝ≥0 => K)
      (μ.restrict (Iio (τ ω))) := integrable_const K
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ≥0 => K)
    hMeas hKInt
  · intro n
    filter_upwards [hIn n] with s hs
    simpa only [Real.norm_eq_abs] using hBound s (Vn n s) hs
  · exact hConv
