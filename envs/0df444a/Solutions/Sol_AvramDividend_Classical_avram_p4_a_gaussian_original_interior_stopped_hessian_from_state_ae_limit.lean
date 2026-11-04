-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_from_state_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:22:45.919883+00:00
-- url     : https://prove2.me/submissions/f21ff7ae-8939-4530-9cd0-7f6b3706de33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_discounted_interior_hessian_state_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_interior_stopped_hessian_correction_dominated_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual source Gaussian Hessian correction on a finite stopped interval
converges from a.e. localised reserve-state convergence. Both approximants
and limit remain strictly inside the stated compact C² band. -/
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
    (hIn : ∀ n, ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      Vn n s ∈ Icc a b)
    (hVin : ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      V s ∈ Icc a b)
    (hMeas : ∀ n, AEStronglyMeasurable (fun s : ℝ≥0 =>
      Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s)))
      (μ.restrict (Iio (τ ω))))
    (hVconv : ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      Tendsto (fun n => Vn n s) atTop (nhds (V s))) :
    Tendsto (fun n => ∫ (s : ℝ≥0),
        Real.exp (-(q * (s : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s))
      ∂(μ.restrict (Iio (τ ω)))) atTop
      (nhds (∫ (s : ℝ≥0), Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (V s))
        ∂(μ.restrict (Iio (τ ω))))) := by
  have hConv : ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      Tendsto (fun n => Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s)))
        atTop (nhds (Real.exp (-(q * (s : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (V s)))) := by
    filter_upwards [hVin, hVconv] with s hs hlim
    exact avram_p4_a_gaussian_original_discounted_interior_hessian_state_tendsto
      X q C w hwC2 (V s) (hBand hs) s (fun n => Vn n s) hlim
  exact avram_p4_a_gaussian_original_interior_stopped_hessian_correction_dominated_limit
    X q hq C w hwC2 a b hBand μ τ ω hFinite Vn V hIn hMeas hConv
