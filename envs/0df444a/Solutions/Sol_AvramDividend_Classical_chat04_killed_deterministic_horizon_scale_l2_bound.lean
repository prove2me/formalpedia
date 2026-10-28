-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_deterministic_horizon_scale_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:34:04.793792+00:00
-- url     : https://prove2.me/submissions/18334f00-27bc-454f-b5c6-61e8af5142ad

import Theorems.Thm_AvramDividend_Classical_chat04_deterministic_horizon_scale_l2_uniform_bound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Notation.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- Restricting a squared discounted scale payoff to a measurable
survival event preserves the explicit deterministic-horizon L² bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t : ℝ≥0) (htN : t ≤ N)
    (S : Set Ω) (hS : MeasurableSet S) :
    Integrable (fun ω =>
      (S.indicator (fun u => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t u)) ω)^2) P ∧
    (∫ ω, (S.indicator (fun u => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t u)) ω)^2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  let f : Ω → ℝ := fun ω =>
    Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
  have hRaw : Integrable (fun ω => (f ω)^2) P ∧
      (∫ ω, (f ω)^2 ∂P) ≤
        ((X.ψ θ - q)⁻¹)^2 *
          Real.exp (2 * θ * (x + 1) +
            (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
    simpa only [f] using
      (chat04_deterministic_horizon_scale_l2_uniform_bound
        X q hq W hW θ x hθ hψ N t htN)
  have hShape :
      (fun ω : Ω => (S.indicator f ω)^2) =
        S.indicator (fun ω => (f ω)^2) := by
    funext ω
    by_cases hm : ω ∈ S
    · simp [Set.indicator_of_mem hm]
    · simp [Set.indicator_of_notMem hm]
  change Integrable (fun ω => (S.indicator f ω)^2) P ∧
    (∫ ω, (S.indicator f ω)^2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0)
  rw [hShape]
  have hInt : Integrable (S.indicator (fun ω => (f ω)^2)) P :=
    hRaw.1.indicator hS
  refine ⟨hInt, ?_⟩
  calc
    (∫ ω, S.indicator (fun u => (f u)^2) ω ∂P) ≤
        ∫ ω, (f ω)^2 ∂P := by
          apply integral_mono hInt hRaw.1
          intro ω
          by_cases hm : ω ∈ S
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm, sq_nonneg]
    _ ≤ _ := hRaw.2