-- Prove2me | solution 1 for DynOpaque.TwoPeriod.benchmark_transparent
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:56:30.660886+00:00
-- url     : https://prove2.me/submissions/e30cca35-d746-45ee-809d-8435464718b3

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

/-- §3.3 Benchmark, p. 11: every transparent policy earns at most
`2 max{vH − cH, vL − cL}`; selling `H` at `vH` in both periods earns `2(vH − cH)`, selling `L` at
`vL` in both periods earns `2(vL − cL)`. -/
theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    (∀ (m : Version) (q₁ q₂ : ℝ),
      transparentProfit vH vL cH cL m q₁ q₂ ≤ 2 * max (vH - cH) (vL - cL)) ∧
    transparentProfit vH vL cH cL Version.H vH vH = 2 * (vH - cH) ∧
    transparentProfit vH vL cH cL Version.L vL vL = 2 * (vL - cL) := by
  have hB : 0 ≤ max (vH-cH) (vL-cL) :=
    le_trans (sub_nonneg.mpr hS.2.2.2.2) (le_max_right _ _)
  have hH := le_max_left (vH-cH) (vL-cL)
  have hL := le_max_right (vH-cH) (vL-cL)
  constructor
  · intro m q₁ q₂
    cases m
    · by_cases h1 : q₁ ≤ vH <;> by_cases h2 : q₂ ≤ vH
      all_goals simp only [transparentProfit,Version.val,Version.cost,h1,h2,ite_true,ite_false,one_mul,zero_mul,add_zero,zero_add] <;> linarith
    · by_cases h1 : q₁ ≤ vL <;> by_cases h2 : q₂ ≤ vL
      all_goals simp only [transparentProfit,Version.val,Version.cost,h1,h2,ite_true,ite_false,one_mul,zero_mul,add_zero,zero_add] <;> linarith
  · constructor <;> simp [transparentProfit,Version.val,Version.cost] <;> ring




