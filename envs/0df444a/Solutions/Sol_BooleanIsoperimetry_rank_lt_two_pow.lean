-- Prove2me | solution 1 for BooleanIsoperimetry.rank_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:30.654833+00:00
-- url     : https://prove2.me/submissions/3bdfb769-3fe8-4464-b505-6b02f96913cc

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (x : Cube n) : rank x < 2 ^ n := by
  classical
  have hlt : rank x < (Finset.univ : Finset (Cube n)).card := by
    apply Finset.card_lt_card
    apply Finset.filter_ssubset.mpr
    exact ⟨x, Finset.mem_univ _, fun h => h.2 <| by tauto⟩
  exact lt_of_lt_of_le hlt (by simp +decide [Finset.card_univ])
end BooleanIsoperimetry
