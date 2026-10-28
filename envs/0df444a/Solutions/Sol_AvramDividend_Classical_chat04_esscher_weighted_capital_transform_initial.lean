-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_capital_transform_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:13:48.07446+00:00
-- url     : https://prove2.me/submissions/fc5bcd45-0cda-4754-9ca1-370353e92d2b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_origin_payoff
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_real_expectation_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X 0 p.2 -
              ((0 : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    ENNReal.ofReal (1 / β) := by
  letI : IsProbabilityMeasure P := X.isProbability
  rw [chat04_esscher_weighted_capital_real_expectation_bridge
    X 0 β θ hβ hθ]
  let g : Ω → ℝ := fun ω =>
    (Real.exp (-β * max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (0 : ℝ≥0) ∧ y = X.X s ω})) / β) *
    Real.exp (θ * X.X 0 ω -
      ((0 : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  have hg : g = fun _ : Ω => 1 / β := by
    funext ω
    exact chat04_esscher_reflected_origin_payoff X ω β θ hβ
  change ENNReal.ofReal (∫ ω, g ω ∂P) = ENNReal.ofReal (1 / β)
  rw [hg]
  simp
