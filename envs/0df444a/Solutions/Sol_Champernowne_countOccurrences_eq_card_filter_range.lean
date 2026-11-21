-- Prove2me | solution 1 for Champernowne.countOccurrences_eq_card_filter_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:36:00.861424+00:00
-- url     : https://prove2.me/submissions/cee97227-8dfa-429e-99f0-e82f7abf97f3

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
public import Theorems.Thm_Champernowne_countOccurrences_cons
public import Theorems.Thm_P2M_Champernowne_countOccurrences_nil__4d47a4d3551b

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w l : List ℕ) :
    countOccurrences w l
      = ((Finset.range (l.length + 1)).filter
          (fun j => w.isPrefixOf (l.drop j))).card := by
  induction l with
  | nil =>
    by_cases h : w.isPrefixOf []
    · simp [countOccurrences_nil', h]
    · simp [countOccurrences_nil', h]
  | cons x xs ih =>
    rw [List.length_cons, Finset.card_filter, Finset.sum_range_succ',
      countOccurrences_cons, ih, Finset.card_filter]
    simp only [List.drop_succ_cons, List.drop_zero]
end Champernowne
