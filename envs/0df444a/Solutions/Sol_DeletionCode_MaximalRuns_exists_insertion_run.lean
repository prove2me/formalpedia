-- Prove2me | solution 1 for DeletionCode.MaximalRuns.exists_insertion_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:20.227425+00:00
-- url     : https://prove2.me/submissions/af684493-e387-44da-89f5-bea6b7fc679e

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_exists_maximal_run
import Theorems.Thm_DeletionCode_MaximalRuns_bit_at_run_index
import Theorems.Thm_DeletionCode_MaximalRuns_eraseIdx_in_run
import Theorems.Thm_DeletionCode_SingleEditScripts_eraseIdx_at_split
import Theorems.Thm_DeletionCode_SingleEditScripts_listLetters_at_split


set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (left right : List Bool) (bit : Bool) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ left ++ bit :: right = pre ++ List.replicate rho bit ++ suffix ∧
      left ++ right = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ left.length ∧ left.length < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  obtain ⟨pre, suffix, rho, runBit, hrho, heq, hstart, hstop, hleft, hright⟩ :=
    exists_maximal_run (left ++ bit :: right) left.length
      (by simp only [List.length_append, List.length_cons]; omega)
  have hbit := bit_at_run_index pre suffix rho runBit left.length hstart hstop
  rw [← heq, SingleEditScripts.listLetters_at_split] at hbit
  subst runBit
  have hshort := eraseIdx_in_run pre suffix rho bit left.length hstart hstop
  rw [← heq, SingleEditScripts.eraseIdx_at_split] at hshort
  exact ⟨pre, suffix, rho, hrho, heq, hshort, hstart, hstop, hleft, hright⟩
end DeletionCode.MaximalRuns
