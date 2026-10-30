-- Prove2me | solution 1 for DerivativeChainContinuation.cubicSixthSharpChainRadius_of_normalized_chain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:02:56.57745+00:00
-- url     : https://prove2.me/submissions/40010d9e-d694-4200-a79d-248a73c54571

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPowerAssemblyTarget
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_cubic_power_sharp_radius_of_strict_normalized_chain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


/-- The normalized existence premise is required; this theorem does not discharge it. -/
theorem solution
    (hchain : SixthCompleteNormalizedChain)
    (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree=3)
    (o : ℂ) (R : ℝ) (hR : 0≤R) (hbound : ∀ x : ℂ,q.eval x=0 → ‖x-o‖≤R) :
    ∃ (z : Fin 18 → ℂ) (a b : ℂ),
      (∀ i,(derivative^[18-(i.val+1)] (q^6)).eval (z i)=0) ∧
      z 0=q.roots.sum/3 ∧ (∀ i : Fin 18, 12 ≤ i.val → z i=z 17) ∧ q.eval (z 17)=0 ∧
      ‖a‖=1 ∧ ‖b‖=1 ∧ (a*starRingEnd ℂ b).re=0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z≤((1+Real.sqrt 10)/3)*R := by
  apply cubic_power_sharp_radius_of_strict_normalized_chain 6 (by norm_num) (17/2) 136
    (by norm_num) (by norm_num) 17 (by rfl) _ q hq hdeg o R hR hbound
  intro β hβR hβI
  obtain ⟨z,hroots,hstart,htail,hmR,hmI⟩:=hchain β hβR hβI
  refine ⟨z,?_,hstart,htail,hmR,hmI⟩
  intro i
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,C_mul,C_ofNat] using hroots i
