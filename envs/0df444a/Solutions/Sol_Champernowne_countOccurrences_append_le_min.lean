-- Prove2me | solution 1 for Champernowne.countOccurrences_append_le_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:20.736272+00:00
-- url     : https://prove2.me/submissions/adcc8ee9-e343-4fbc-8434-386c9d818184

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_prefix_of_prefix_append
public import Theorems.Thm_Champernowne_countOccurrences_cons
public import Theorems.Thm_Champernowne_isPrefixOf_append_of_isPrefixOf


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w a b : List ℕ) :
    countOccurrences w (a ++ b)
      ≤ countOccurrences w a + countOccurrences w b
        + min w.length a.length := by
  induction a with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.min_zero, Nat.add_zero]
    exact Nat.le_add_left _ _
  | cons x a' ih =>
    rw [List.cons_append, countOccurrences_cons, countOccurrences_cons]
    have hlc : (x :: a').length = a'.length + 1 := by simp
    by_cases h : w.isPrefixOf (x :: (a' ++ b))
    · by_cases h' : w.isPrefixOf (x :: a')
      · simp only [h, h']
        omega
      · -- straddling window: `w` overhangs the end of `x :: a'`
        have hlen : (x :: a').length < w.length := by
          rcases Nat.lt_or_ge (x :: a').length w.length with hlt | hge
          · exact hlt
          · refine absurd ?_ h'
            rw [List.isPrefixOf_iff_prefix] at h ⊢
            exact prefix_of_prefix_append
              (by rwa [← List.cons_append] at h) hge
        simp only [h, h', ite_true]
        omega
    · have h' : ¬ w.isPrefixOf (x :: a') := by
        intro hc
        apply h
        rw [← List.cons_append]
        exact isPrefixOf_append_of_isPrefixOf b hc
      simp only [h, h']
      omega
end Champernowne
