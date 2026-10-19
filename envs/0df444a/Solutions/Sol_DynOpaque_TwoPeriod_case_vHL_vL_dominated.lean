-- Prove2me | solution 1 for DynOpaque.TwoPeriod.case_vHL_vL_dominated
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:19.874838+00:00
-- url     : https://prove2.me/submissions/94a01884-33b1-45c1-869e-bf309a002094

import Definitions.Def_DynOpaque_TwoPeriod_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Function
import Lean.Elab.Tactic.Omega
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

open DynOpaque.TwoPeriod

/-- Proof of Proposition 1, p. 30: the case `p₁ = vHL`, `p₂ = vL` is never optimal — every
value of objective (4) on the box is at most the larger of some value of objective (3) on the box
and the best transparent profit `2 max{vH − cH, vL − cL}`. -/
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    ∀ x ∈ box, ∃ y ∈ box,
      obj4 vH vL cH cL x.1 x.2 ≤ max (obj3 vH vL cH cL α y.1 y.2) (2 * max (vH - cH) (vL - cL)) := by
  intro x hx
  refine ⟨(x.1,x.1),⟨hx.1,hx.1⟩,?_⟩
  have hd := mul_nonneg (sub_pos.mpr hS.2.1).le hx.2.1
  have hb := le_max_right (vH-cH) (vL-cL)
  by_cases ht : x.1 * (vHL vH vL - x.1*cH-(1-x.1)*cL) ≤ max (vH-cH) (vL-cL)
  · apply le_max_of_le_right
    dsimp [obj4]
    nlinarith
  · apply le_max_of_le_left
    dsimp [obj4,obj3]
    nlinarith



