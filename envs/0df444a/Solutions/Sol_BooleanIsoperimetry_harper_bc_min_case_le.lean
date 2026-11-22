-- Prove2me | solution 1 for BooleanIsoperimetry.harper_bc_min_case_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:03:07.6697+00:00
-- url     : https://prove2.me/submissions/44263c38-a27e-4501-8527-3509c4ebd4f5

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
public import Theorems.Thm_BooleanIsoperimetry_harper_subadd_le
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : a ≤ H n b)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + H n b := by
  have hsucc := H_succ_cascade hcasc
  have hcb := canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc
  have key := harper_subadd_le n ih ha hb hb_le_a hcase
  rw [hsucc, hcb] at key
  exact key
end BooleanIsoperimetry
