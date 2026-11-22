-- Prove2me | solution 1 for BooleanIsoperimetry.rank_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:19.597462+00:00
-- url     : https://prove2.me/submissions/88579471-f2ec-4c85-97a3-198c627aaf58

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
theorem _root_.solution {n : ℕ} {x y : Cube n} (h : simplicialLt x y) :
    rank x < rank y := by
  classical
  refine Finset.card_lt_card ?_
  simp only [Finset.ssubset_def, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ,
    true_and]
  unfold simplicialLt at *
  unfold simplicialLe at *
  grind
end BooleanIsoperimetry
