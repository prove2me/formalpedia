-- Prove2me | solution 1 for DynOpaque.TwoPeriod.objectives_3_to_6
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:06.547311+00:00
-- url     : https://prove2.me/submissions/a629adf2-2446-41f8-ad1d-54a0e7deac59

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

/-- Displays (3)–(6), pp. 11–13: at the four candidate price pairs, profit (2) is the
objective printed for that pair. -/
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) (ξ₁ ξ₂ : ℝ) :
    opaqueProfit vH vL cH cL α (vHL vH vL) (vHL vH vL) ξ₁ ξ₂ = obj3 vH vL cH cL α ξ₁ ξ₂ ∧
    opaqueProfit vH vL cH cL α (vHL vH vL) vL ξ₁ ξ₂ = obj4 vH vL cH cL ξ₁ ξ₂ ∧
    opaqueProfit vH vL cH cL α vL (vHL vH vL) ξ₁ ξ₂ = obj5 vH vL cH cL α ξ₁ ξ₂ ∧
    opaqueProfit vH vL cH cL α vL vL ξ₁ ξ₂ = obj6 vL cH cL ξ₁ ξ₂ := by
  have hm (h : ℝ) : frac vH vL h (vHL vH vL) = h := by
    have hyes : buys vH vL (estimate 1) (vHL vH vL) := by
      unfold buys estimate estimateK vHL
      norm_num
      linarith
    have hno : ¬ buys vH vL (estimate 0) (vHL vH vL) := by
      unfold buys estimate estimateK vHL
      norm_num
      linarith [hS.1]
    simp [frac, hyes, hno]
  have hl (h : ℝ) : frac vH vL h vL = 1 := by
    have hyes : buys vH vL (estimate 1) vL := by
      unfold buys estimate estimateK
      norm_num
      linarith [hS.1]
    have hzero : buys vH vL (estimate 0) vL := by
      unfold buys estimate estimateK
      norm_num
    simp [frac, hyes, hzero]
  simp [opaqueProfit, hm, hl, margin, obj3, obj4, obj5, obj6] <;> ring



