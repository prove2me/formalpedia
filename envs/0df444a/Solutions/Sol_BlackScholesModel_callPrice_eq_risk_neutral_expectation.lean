-- Prove2me | solution 1 for BlackScholesModel.callPrice_eq_risk_neutral_expectation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:37:10.126931+00:00
-- url     : https://prove2.me/submissions/5ce2f0a5-7a31-45e9-9118-117c0f35b81b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_asset_or_nothing_value
import Theorems.Thm_BlackScholesModel_cash_or_nothing_value
import Theorems.Thm_BlackScholesModel_call_payoff_integral_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    callPrice K r σ T S t
      = Real.exp (-r * (T - t))
          * ∫ z, max (terminalPrice S r σ (T - t) z - K) 0 ∂(gaussianReal 0 1) := by
  let I : ℝ := ∫ z in {z | K < terminalPrice S r σ (T - t) z},
    terminalPrice S r σ (T - t) z ∂(gaussianReal 0 1)
  let P : ℝ := (gaussianReal 0 1).real {z | K < terminalPrice S r σ (T - t) z}
  have hAsset :
      Real.exp (-r * (T - t)) * I =
        S * stdNormalCDF (dPlus S K r σ (T - t)) :=
    (asset_or_nothing_value K r σ T S t hK hσ hS ht).1
  have hCash :
      Real.exp (-r * (T - t)) * P =
        Real.exp (-r * (T - t)) * stdNormalCDF (dMinus S K r σ (T - t)) :=
    (cash_or_nothing_value K r σ T S t hK hσ hS ht).1
  have hPayoff :
      (∫ z, max (terminalPrice S r σ (T - t) z - K) 0 ∂(gaussianReal 0 1)) =
        I - K * P := call_payoff_integral_decomposition K r σ T S t hK hσ hS ht
  rw [hPayoff]
  unfold callPrice
  calc
    stdNormalCDF (dPlus S K r σ (T - t)) * S -
        stdNormalCDF (dMinus S K r σ (T - t)) * K * Real.exp (-r * (T - t))
      = (Real.exp (-r * (T - t)) * I) -
        K * (Real.exp (-r * (T - t)) * P) := by
          rw [hAsset, hCash]
          ring
    _ = Real.exp (-r * (T - t)) * (I - K * P) := by ring
