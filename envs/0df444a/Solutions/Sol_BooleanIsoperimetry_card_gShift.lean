-- Prove2me | solution 1 for BooleanIsoperimetry.card_gShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:35.330581+00:00
-- url     : https://prove2.me/submissions/4c60ce2f-1bdc-4efb-91d3-87de77527208

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
theorem _root_.solution {n : ℕ} (v : Cube n) : (gShift v).card = v.card - 1 := by
  rcases Finset.eq_empty_or_nonempty v with (rfl | hne) <;>
    simp_all +decide only [gShift, Finset.not_nonempty_empty, ↓reduceDIte, Finset.card_empty,
      zero_tsub]
  exact Finset.card_erase_of_mem (Finset.min'_mem _ hne)
end BooleanIsoperimetry
