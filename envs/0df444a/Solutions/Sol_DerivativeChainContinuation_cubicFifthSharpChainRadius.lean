-- Prove2me | solution 1 for DerivativeChainContinuation.cubicFifthSharpChainRadius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:23:09.323283+00:00
-- url     : https://prove2.me/submissions/ea9ff9d4-54de-4aa2-a2a2-55db7bf8796f

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_cubic_power_sharp_radius_of_strict_normalized_chain
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_chain_strict
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainContinuation in
theorem solution (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x - o‖ ≤ R) :
    ∃ (z : Fin 15 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[15 - (i.val + 1)] (q^5)).eval (z i) = 0) ∧
      z 0 = q.roots.sum / 3 ∧
      (∀ i : Fin 15, 10 ≤ i.val → z i = z 14) ∧ q.eval (z 14) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a * starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a * z i).re) ∧ Monotone (fun i => (b * z i).re) ∧
      chainCost z ≤ sharpCubicConstant * R := by
  apply cubic_power_sharp_radius_of_strict_normalized_chain 5 (by norm_num) 7 91
    (by norm_num) (by norm_num) 14 (by rfl) _ q hq hdeg o R hR hbound
  intro β hβR hβI
  obtain ⟨z,hroots,hstart,htail,_,hmR,hmI,_⟩ := normalized_fifth_chain_strict β hβR hβI
  refine ⟨z,?_,hstart,htail,hmR,hmI⟩
  intro i
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,C_mul,C_ofNat] using hroots i
