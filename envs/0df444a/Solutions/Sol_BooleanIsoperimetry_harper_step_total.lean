-- Prove2me | solution 1 for BooleanIsoperimetry.harper_step_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:57:12.169795+00:00
-- url     : https://prove2.me/submissions/15c3ea56-e1af-41c0-aa96-44eca2f3ca1e

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_boundaryCostH_comm
public import Theorems.Thm_BooleanIsoperimetry_harper_step_total_le_case

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1)) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by
  rcases le_total b a with hba | hab
  · exact harper_step_total_le_case n ih ha hb hba
  · rw [boundaryCostH_comm, Nat.add_comm a b]
    exact harper_step_total_le_case n ih hb ha hab
end BooleanIsoperimetry
