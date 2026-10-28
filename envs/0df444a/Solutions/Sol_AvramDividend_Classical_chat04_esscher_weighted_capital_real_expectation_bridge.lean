-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_capital_real_expectation_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:47:13.036533+00:00
-- url     : https://prove2.me/submissions/7358fa74-81c3-4f0a-9eda-e8c21cd27b80

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_infimum_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Replace the extended-real reflected-infimum transform by its finite
    ordinary expectation, using integrability of the Esscher weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    ENNReal.ofReal (∫ ω : Ω,
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) := by
  let a : Ω → ℝ := fun ω =>
    Real.exp (-β * max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β
  let b : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X t ω -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  let f : Ω → ℝ := fun ω => a ω * b ω
  have ha : ∀ ω, 0 ≤ a ω := by
    intro ω
    dsimp [a]
    positivity
  have hf : Integrable f P := by
    simpa only [f, a, b] using
      chat04_esscher_weighted_reflected_infimum_integrable X t β θ hβ hθ
  have hfn : ∀ ω, 0 ≤ f ω := by
    intro ω
    exact mul_nonneg (ha ω) (Real.exp_pos _).le
  rw [chat04_esscher_weighted_capital_reflected_infimum_transform X t β θ hβ]
  change (∫⁻ ω, ENNReal.ofReal (a ω) * ENNReal.ofReal (b ω) ∂P) =
    ENNReal.ofReal (∫ ω, f ω ∂P)
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (f ω) ∂P := by
      refine lintegral_congr fun ω => ?_
      exact (ENNReal.ofReal_mul (ha ω)).symm
    _ = ENNReal.ofReal (∫ ω, f ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hf
        (Filter.Eventually.of_forall hfn)).symm
