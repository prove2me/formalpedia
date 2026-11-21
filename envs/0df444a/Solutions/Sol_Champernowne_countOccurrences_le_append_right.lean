-- Prove2me | solution 1 for Champernowne.countOccurrences_le_append_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:42.112894+00:00
-- url     : https://prove2.me/submissions/3a4ed722-bde1-4872-9f11-e1dc2427b205

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_if_isPrefixOf_le_countOccurrences
public import Theorems.Thm_Champernowne_countOccurrences_cons
public import Theorems.Thm_Champernowne_isPrefixOf_append_of_isPrefixOf
public import Theorems.Thm_P2M_Champernowne_countOccurrences_nil__4d47a4d3551b


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w a b : List ℕ) :
    countOccurrences w a ≤ countOccurrences w (a ++ b) := by
  induction a with
  | nil =>
    simp only [List.nil_append]
    rw [countOccurrences_nil']
    by_cases hw0 : w.isPrefixOf []
    · have hwnil : w = [] := by
        simpa [List.isPrefixOf_iff_prefix, List.prefix_nil] using hw0
      subst hwnil
      have h := if_isPrefixOf_le_countOccurrences [] b
      simpa [List.isPrefixOf_iff_prefix, List.nil_prefix, hw0] using h
    · simp [hw0]
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
