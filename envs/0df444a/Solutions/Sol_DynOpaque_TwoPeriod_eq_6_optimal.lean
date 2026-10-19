-- Prove2me | solution 1 for DynOpaque.TwoPeriod.eq_6_optimal
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:09.887102+00:00
-- url     : https://prove2.me/submissions/cba8425d-cec5-4207-a013-7eeea775b2ac

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

/-- Claim after display (6), p. 13: with `p₁ = p₂ = vL` the optimal offering decisions are
`ξ₁ = ξ₂ = 0`, i.e. transparent selling of product `L`, earning `2(vL − cL)`. -/
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    IsOptimalOffering (obj6 vL cH cL) 0 0 ∧ obj6 vL cH cL 0 0 = 2 * (vL - cL) := by
  have hd : 0 ≤ cH - cL := (sub_pos.mpr hS.2.1).le
  constructor
  · constructor
    · exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
    · intro x hx
      have h1 := mul_nonneg hd hx.1.1
      have h2 := mul_nonneg hd hx.2.1
      dsimp [obj6]
      nlinarith
  · dsimp [obj6]
    ring



