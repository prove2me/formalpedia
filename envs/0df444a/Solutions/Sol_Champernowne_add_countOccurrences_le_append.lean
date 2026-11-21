-- Prove2me | solution 1 for Champernowne.add_countOccurrences_le_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:36:40.051433+00:00
-- url     : https://prove2.me/submissions/c87f342c-ad7a-4b02-b650-95291b231973

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
public import Theorems.Thm_Champernowne_countOccurrences_cons
public import Theorems.Thm_Champernowne_countOccurrences_nil
public import Theorems.Thm_Champernowne_isPrefixOf_append_of_isPrefixOf

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {w : List ℕ} (hw : w ≠ [])
    (a b : List ℕ) :
    countOccurrences w a + countOccurrences w b
      ≤ countOccurrences w (a ++ b) := by
  induction a with
  | nil => simp [countOccurrences_nil hw]
  | cons x a' ih =>
    rw [List.cons_append, countOccurrences_cons, countOccurrences_cons]
    have hmono : (if w.isPrefixOf (x :: a') then 1 else 0)
        ≤ if w.isPrefixOf (x :: (a' ++ b)) then 1 else 0 := by
      by_cases h : w.isPrefixOf (x :: a')
      · have h2 : w.isPrefixOf (x :: (a' ++ b)) := by
          rw [← List.cons_append]
          exact isPrefixOf_append_of_isPrefixOf b h
        simp [h, h2]
      · simp [h]
    omega
end Champernowne
