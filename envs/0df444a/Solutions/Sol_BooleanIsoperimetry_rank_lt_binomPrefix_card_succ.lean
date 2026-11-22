-- Prove2me | solution 1 for BooleanIsoperimetry.rank_lt_binomPrefix_card_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:48.205954+00:00
-- url     : https://prove2.me/submissions/c1c11d14-9e03-47bd-87d2-9a7e47b8ac70

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (w : Cube n) :
    rank w < binomPrefix n (w.card + 1) := by
  exact (rank_lt_binomPrefix_iff w).mpr (Nat.lt_succ_self _)
end BooleanIsoperimetry
