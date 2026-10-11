-- Prove2me | solution 1 for BlackScholesModel.put_theta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:37:21.506996+00:00
-- url     : https://prove2.me/submissions/e39efe22-9d8e-4908-96a8-a61707006b9f

import Theorems.Thm_BlackScholesModel_call_theta
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
    HasDerivAt (fun t' => putPrice K r σ T S t')
      (-(S * stdNormalPDF (dPlus S K r σ (T - t)) * σ) / (2 * Real.sqrt (T - t))
        + r * K * Real.exp (-r * (T - t)) * stdNormalCDF (-dMinus S K r σ (T - t))) t := by
  have hparity : (fun u : ℝ => putPrice K r σ T S u) =
      (fun u : ℝ => K * Real.exp (-r * (T - u)) - S + callPrice K r σ T S u) := by
    funext u
    exact put_call_parity K r σ T S u
  have hlin : HasDerivAt (fun u : ℝ => -r * (T - u)) r t := by
    convert ((hasDerivAt_id t).const_mul r).const_add (-r * T) using 1 <;>
      first
      | rfl
      | (funext x; dsimp [id]; ring)
      | ring
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-r * (T - u)))
      (Real.exp (-r * (T - t)) * r) t :=
    (Real.hasDerivAt_exp _).comp t hlin
  have hdiscount := hexp.const_mul K
  have hcall := call_theta K r σ T S t hK hσ hS ht
  have hderiv : HasDerivAt
      (fun u : ℝ => K * Real.exp (-r * (T - u)) - S + callPrice K r σ T S u)
      (K * (Real.exp (-r * (T - t)) * r) +
         (-(S * stdNormalPDF (dPlus S K r σ (T - t)) * σ) / (2 * Real.sqrt (T - t))
         - r * K * Real.exp (-r * (T - t)) * stdNormalCDF (dMinus S K r σ (T - t)))) t := by
    convert (hdiscount.sub (hasDerivAt_const t S)).add hcall using 1 <;> (try { funext z }) <;> (first | rfl | ring | simp [sub_eq_add_neg])
  rw [hparity, stdNormalCDF_neg]
  convert hderiv using 1 <;> (try { funext z }) <;> (first | rfl | ring | simp [sub_eq_add_neg])