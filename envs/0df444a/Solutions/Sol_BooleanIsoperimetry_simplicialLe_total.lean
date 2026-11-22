-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLe_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:02.309464+00:00
-- url     : https://prove2.me/submissions/954293a9-9cd0-4770-a073-fdd944d27252

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (a b : Cube n) : simplicialLe a b ∨ simplicialLe b a := by
  unfold simplicialLe
  rcases lt_trichotomy a.card b.card with h_lt | h_eq | h_gt
  · left; left; exact h_lt
  · rcases le_total (cubeToNat a) (cubeToNat b) with h_nat_le | h_nat_ge
    · right; right; exact ⟨h_eq.symm, h_nat_le⟩
    · left; right; exact ⟨h_eq, h_nat_ge⟩
  · right; left; exact h_gt
end BooleanIsoperimetry
