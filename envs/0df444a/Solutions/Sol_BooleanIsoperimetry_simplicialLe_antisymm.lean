-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLe_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:38.289374+00:00
-- url     : https://prove2.me/submissions/46d26b9d-a5d5-496a-baa0-41d015410df8

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_inj

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (a b : Cube n)
    (hab : simplicialLe a b) (hba : simplicialLe b a) : a = b := by
  unfold simplicialLe at hab hba
  rcases hab with h_a_lt_b | ⟨h_card_eq, h_nat_le⟩
  · rcases hba with h_b_lt_a | ⟨h_card_eq2, _⟩
    · omega
    · omega
  · rcases hba with h_b_lt_a | ⟨_, h_nat_le2⟩
    · omega
    · have h_nat_eq : cubeToNat a = cubeToNat b := le_antisymm h_nat_le2 h_nat_le
      exact cubeToNat_inj h_nat_eq
end BooleanIsoperimetry
