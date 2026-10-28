-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_capital_transform_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:34:14.206423+00:00
-- url     : https://prove2.me/submissions/52cbbbe0-aa5b-4450-a4ea-3ee5433bddda

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_real_expectation_bridge
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_transform_unit_bound
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) ≤
    ENNReal.ofReal (1 / β) := by
  rw [chat04_esscher_weighted_capital_real_expectation_bridge
    X t β θ hβ hθ]
  exact ENNReal.ofReal_le_ofReal
    (chat04_esscher_weighted_reflected_transform_unit_bound
      X t β θ hβ hθ).2
