-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_finite_state_dividend_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:23:32.049312+00:00
-- url     : https://prove2.me/submissions/9c3bcde2-7cc7-4fdf-bcae-3eef16dd730f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_valued_reserve
import Theorems.Thm_AvramDividend_Classical_levy_exponential_one_step_dividend_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} [Fintype ι]
    (p : Ω → ι)
    (hp : ∀ i, MeasurableSet[𝓕 s] {ω : Ω | p ω = i})
    (u a : ι → ℝ) (θ q : ℝ)
    (hθ : 1 ≤ θ) (ha : ∀ i, 0 ≤ a i)
    (hua : ∀ i, a i ≤ u i) (hψ : X.ψ θ ≤ q)
    (hI : ∀ i, Integrable
      (fun ω => Real.exp (θ * (u i - a i + X.X (t - s) ω))) P) :
    ∀ᵐ ω ∂P,
      a (p ω) + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (P[(fun η => Real.exp (θ *
          (u (p η) - a (p η) + (X.X t η - X.X s η)))) | 𝓕 s]) ω ≤
      Real.exp (θ * u (p ω)) := by
  have hM : Measurable (fun z : ℝ => Real.exp (θ * z)) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).measurable
  have hCE :=
    levy_increment_condExp_finite_valued_reserve
      X s t hst p hp (fun i => u i - a i)
      (fun z => Real.exp (θ * z)) hM hI
  filter_upwards [hCE] with ω hω
  rw [hω]
  exact levy_exponential_one_step_dividend_budget
    X (t - s) θ q (u (p ω)) (a (p ω))
    hθ (ha (p ω)) (hua (p ω)) hψ
