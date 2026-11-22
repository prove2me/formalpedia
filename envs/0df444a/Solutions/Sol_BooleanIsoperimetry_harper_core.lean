-- Prove2me | solution 1 for BooleanIsoperimetry.harper_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:04:28.983815+00:00
-- url     : https://prove2.me/submissions/2feb79dd-a96c-45b3-8a21-6bcd670eeb74

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
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution :
    ∀ (n a b : ℕ), a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b ha hb
    have hS : a + b ≤ 2 ^ (n + 1) := by
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega
    obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hS
    rw [H_succ_cascade hcasc]
    exact harper_bc_min n ih ha hb hp hq hpq hcasc
end BooleanIsoperimetry
