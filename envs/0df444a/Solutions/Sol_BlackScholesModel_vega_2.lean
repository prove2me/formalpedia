-- Prove2me | solution 2 for BlackScholesModel.vega
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:21:10.069046+00:00
-- url     : https://prove2.me/submissions/a56d3567-28f9-41f1-a9e4-7c562394b126

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_call_vega
import Theorems.Thm_BlackScholesModel_put_call_parity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Both options share the same volatility derivative by put-call parity. -/
theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun σ' => callPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ ∧
    HasDerivAt (fun σ' => putPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ := by
  have hC := call_vega K r σ T S t hK hσ hS ht
  have hfun :
      (fun v : ℝ => putPrice K r v T S t) =
      (fun v : ℝ => (K * Real.exp (-r * (T - t)) - S) +
        callPrice K r v T S t) := by
    funext v
    convert put_call_parity K r v T S t using 1 <;> ring
  constructor
  · exact hC
  · rw [hfun]
    exact hC.const_add (K * Real.exp (-r * (T - t)) - S)
