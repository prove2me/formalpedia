-- Prove2me | solution 1 for AvramDividend.Classical.levy_grid_upper_exit_discount_bound_complete
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:48:42.192425+00:00
-- url     : https://prove2.me/submissions/da58d9a0-0be3-4824-a51e-d365ba26248e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_grid_upper_exit_discount_integrable
import Theorems.Thm_AvramDividend_Classical_levy_grid_upper_exit_exp_bound
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A positive-Laplace-parameter Lévy grid stop has exponential upper-exit discount bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → NNReal) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 ≤ X.ψ θ)
    (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω) :
    (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
      (fun z => Real.exp (-((clock (K z)) : ℝ) * X.ψ θ)) ω ∂P) ≤
      Real.exp (-θ * upper) := by
  have hpart : Integrable
      ({ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun ω => Real.exp
          (-((clock (K ω)) : ℝ) * X.ψ θ))) P :=
    levy_grid_upper_exit_discount_integrable
      X clock H hH lower upper m K hK (X.ψ θ) hψ
  exact levy_grid_upper_exit_exp_bound
    X clock hc hc0 H hH θ hθ lower upper m K hK hpart
