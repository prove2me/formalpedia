-- Prove2me | solution 2 for BlackScholesModel.callPrice_eq_risk_neutral_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:02:42.005145+00:00
-- url     : https://prove2.me/submissions/7485a3be-2d4a-4a3b-81cd-57ea654103a3

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_callPayoff_integral_decomposition
import Theorems.Thm_BlackScholesModel_cash_or_nothing_value
import Theorems.Thm_BlackScholesModel_asset_or_nothing_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Risk-neutral call valuation from the cash and asset digital claims. -/
theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    callPrice K r σ T S t
      = Real.exp (-r * (T - t))
          * ∫ z, max (terminalPrice S r σ (T - t) z - K) 0
              ∂(gaussianReal 0 1) := by
  let τ : ℝ := T - t
  have hτ : 0 < τ := sub_pos.mpr ht
  have hasset := (asset_or_nothing_value K r σ T S t hK hσ hS ht).1
  have hcash := (cash_or_nothing_value K r σ T S t hK hσ hS ht).1
  have hdecomp :=
    callPayoff_integral_decomposition K r σ τ S hK hσ hτ hS
  change callPrice K r σ T S t =
    Real.exp (-r * τ) *
      (∫ z, max (terminalPrice S r σ τ z - K) 0
        ∂(gaussianReal 0 1))
  rw [hdecomp]
  calc
    callPrice K r σ T S t =
      S * stdNormalCDF (dPlus S K r σ τ) -
      K * Real.exp (-r * τ) *
        stdNormalCDF (dMinus S K r σ τ) := by
          dsimp [callPrice, τ]
          ring
    _ = Real.exp (-r * τ) *
          (∫ z in {z | K < terminalPrice S r σ τ z},
            terminalPrice S r σ τ z ∂(gaussianReal 0 1)) -
        K * (Real.exp (-r * τ) *
          (gaussianReal 0 1).real
            {z | K < terminalPrice S r σ τ z}) := by
          rw [hasset, hcash]
          ring
    _ = Real.exp (-r * τ) *
        ((∫ z in {z | K < terminalPrice S r σ τ z},
          terminalPrice S r σ τ z ∂(gaussianReal 0 1)) -
        K * (gaussianReal 0 1).real
          {z | K < terminalPrice S r σ τ z}) := by ring
