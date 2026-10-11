-- Prove2me | solution 1 for BlackScholesModel.vega
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:28:22.377309+00:00
-- url     : https://prove2.me/submissions/9f22df61-5c86-41cc-a282-21b29d670b3b

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

theorem solution (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun σ' => callPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ ∧
    HasDerivAt (fun σ' => putPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ := by
  have hcall := call_vega K r σ T S t hK hσ hS ht
  have hparity : (fun u : ℝ => putPrice K r u T S t) =
      (fun u : ℝ => (K * Real.exp (-r * (T - t)) - S) + callPrice K r u T S t) := by
    funext u
    exact put_call_parity K r u T S t
  constructor
  · exact hcall
  · rw [hparity]
    exact hcall.const_add (K * Real.exp (-r * (T - t)) - S)
