-- Prove2me | solution 1 for DerivativeChainContinuation.cubicCubeSharpChainRadius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:21:03.801997+00:00
-- url     : https://prove2.me/submissions/bd007b75-2377-40d3-a8cc-2ceac1f84ec6

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_cubic_power_sharp_radius_of_strict_normalized_chain
import Theorems.Thm_DerivativeChainPrivate_normalized_cubic_cube_chain
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainContinuation in
theorem solution (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x-o‖ ≤ R) :
    ∃ (z : Fin 9 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[9-(i.val+1)] (q^3)).eval (z i)=0) ∧
      z 0=q.roots.sum/3 ∧ (∀ i : Fin 9, 6 ≤ i.val → z i=z 8) ∧ q.eval (z 8)=0 ∧
      ‖a‖=1 ∧ ‖b‖=1 ∧ (a*starRingEnd ℂ b).re=0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by
  apply cubic_power_sharp_radius_of_strict_normalized_chain 3 (by norm_num) 4 28
    (by norm_num) (by norm_num) 8 (by rfl) _ q hq hdeg o R hR hbound
  intro β hβR hβI
  obtain ⟨z,hroots,hstart,h67,h78,_,_,hmR,hmI,_⟩ := normalized_cubic_cube_chain β hβR hβI.le
  refine ⟨z,?_,hstart,?_,hmR,hmI⟩
  · intro i
    simpa only [Complex.ofReal_ofNat,C_mul,C_ofNat] using hroots i
  · intro i hi
    have hh : i.val=6 ∨ i.val=7 ∨ i.val=8 := by omega
    rcases hh with hh|hh|hh
    · have he : i=(6:Fin 9) := Fin.ext hh
      rw [he]; exact h67.trans h78
    · have he : i=(7:Fin 9) := Fin.ext hh
      rwa [he]
    · have he : i=(8:Fin 9) := Fin.ext hh
      rw [he]
