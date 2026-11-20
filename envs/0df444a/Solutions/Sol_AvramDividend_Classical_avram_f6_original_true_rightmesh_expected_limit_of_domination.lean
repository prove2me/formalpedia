-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_true_rightmesh_expected_limit_of_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:25:13.646877+00:00
-- url     : https://prove2.me/submissions/6db7ffaf-6a31-4e9c-b5fa-a5c84016fe98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (σ τ : Ω → ℝ≥0)
    (ρ : ℕ → Ω → ℝ≥0 := fun m ω =>
      min (τ ω) (σ ω + 1 / ((m : ℝ≥0) + 1)))
    (V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal))
    (R : (Ω → ℝ≥0) → Ω → ℝ := fun s ω =>
      Real.exp (-(q * (s ω : ℝ))) *
        V (if s ω = 0 ∨ (s ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (s ω) ω - rightLimit D (s ω) ω
          else riskProcess X x D (s ω) ω) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (s ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)
    (bound : Ω → ℝ)
    (hbound : Integrable bound P)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω => R (ρ m) ω) P)
    (hdom : ∀ m, ∀ᵐ ω ∂P, ‖R (ρ m) ω‖ ≤ bound ω)
    (hlim : ∀ᵐ ω ∂P,
      Tendsto (fun m => R (ρ m) ω) atTop (𝓝 (R σ ω))) :
    Tendsto (fun m => ∫ ω, R (ρ m) ω ∂P) atTop
      (𝓝 (∫ ω, R σ ω ∂P)) := by
  exact tendsto_integral_of_dominated_convergence
    bound hMeas hbound hdom hlim
