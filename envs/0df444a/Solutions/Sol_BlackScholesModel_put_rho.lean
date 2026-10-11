-- Prove2me | solution 1 for BlackScholesModel.put_rho
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:20:22.257399+00:00
-- url     : https://prove2.me/submissions/95637a20-8693-42b0-8d27-c5ea702200a5

import Theorems.Thm_BlackScholesModel_call_rho
import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_put_call_parity
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun r' => putPrice K r' σ T S t)
      (-(K * (T - t) * Real.exp (-r * (T - t)) * stdNormalCDF (-dMinus S K r σ (T - t)))) r := by
  have hparity : (fun u : ℝ => putPrice K u σ T S t) =
      (fun u : ℝ => K * Real.exp (-u * (T - t)) - S + callPrice K u σ T S t) := by
    funext u
    exact put_call_parity K u σ T S t
  have hlin : HasDerivAt (fun u : ℝ => -u * (T - t)) (-(T - t)) r := by
    convert (hasDerivAt_id r).neg.mul_const (T - t) using 1 <;> (try { funext z }) <;> (first | rfl | ring | simp [sub_eq_add_neg])
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u * (T - t)))
      (Real.exp (-r * (T - t)) * (-(T - t))) r :=
    (Real.hasDerivAt_exp _).comp r hlin
  have hdiscount := hexp.const_mul K
  have hcall := call_rho K r σ T S t hK hσ hS ht
  have hderiv : HasDerivAt
      (fun u : ℝ => K * Real.exp (-u * (T - t)) - S + callPrice K u σ T S t)
      (K * (Real.exp (-r * (T - t)) * (-(T - t))) +
        K * (T - t) * Real.exp (-r * (T - t)) * stdNormalCDF (dMinus S K r σ (T - t))) r := by
    convert (hdiscount.sub (hasDerivAt_const r S)).add hcall using 1 <;> (try { funext z }) <;> (first | rfl | ring | simp [sub_eq_add_neg])
  rw [hparity, stdNormalCDF_neg]
  convert hderiv using 1 <;> (try { funext z }) <;> (first | rfl | ring | simp [sub_eq_add_neg])
