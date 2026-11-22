-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_card_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:40.799544+00:00
-- url     : https://prove2.me/submissions/a791da76-ca31-4bc8-a8c7-ed265df31e41

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
    binomPrefix n w.card ≤ rank w := by
  by_contra hlt
  push Not at hlt
  exact absurd ((rank_lt_binomPrefix_iff w).mp hlt) (lt_irrefl _)
end BooleanIsoperimetry
