-- Prove2me | solution 1 for BlackScholesModel.put_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:20:11.464321+00:00
-- url     : https://prove2.me/submissions/a5371584-59b9-47e0-8d78-41a998a6ebcc

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_call_delta
import Theorems.Thm_BlackScholesModel_put_call_parity
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun S' => putPrice K r σ T S' t)
      (-stdNormalCDF (-dPlus S K r σ (T - t))) S ∧
    -stdNormalCDF (-dPlus S K r σ (T - t)) = stdNormalCDF (dPlus S K r σ (T - t)) - 1 := by
  have hparity : (fun z : ℝ => putPrice K r σ T z t) =
      (fun z : ℝ => K * Real.exp (-r * (T - t)) - z + callPrice K r σ T z t) := by
    funext z
    exact put_call_parity K r σ T z t
  have hcall := call_delta K r σ T S t hK hσ hS ht
  have hderiv : HasDerivAt
      (fun z : ℝ => K * Real.exp (-r * (T - t)) - z + callPrice K r σ T z t)
      (stdNormalCDF (dPlus S K r σ (T - t)) - 1) S := by
    convert ((hasDerivAt_const S (K * Real.exp (-r * (T - t)))).sub
      (hasDerivAt_id S)).add hcall using 1 <;> (try { funext z }) <;> (first | rfl | ring | simp [sub_eq_add_neg])
  constructor
  · rw [hparity]
    rw [stdNormalCDF_neg]
    convert hderiv using 1 <;> (try { funext z }) <;> (first | rfl | ring | simp [sub_eq_add_neg])
  · rw [stdNormalCDF_neg]
    ring
