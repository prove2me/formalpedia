-- Prove2me | solution 1 for DeletionCode.MaximalRuns.exists_insertion_run_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:16.682947+00:00
-- url     : https://prove2.me/submissions/b32d329c-bbb7-43e7-a4c2-3c678d3dbfab

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_constantOn_block
import Theorems.Thm_DeletionCode_MaximalRuns_exists_insertion_run
import Theorems.Thm_DeletionCode_SingleEditScripts_insert_split
import Theorems.Thm_DeletionCode_UniqueRuns_insert_constant_length_le


set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (left right : List Bool) (bit : Bool) (k : ℕ)
    (hx : KUnique (listLetters (left ++ right)) (left ++ right).length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ rho ≤ k + 1 ∧
      left ++ bit :: right = pre ++ List.replicate rho bit ++ suffix ∧
      left ++ right = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ left.length ∧ left.length < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  obtain ⟨pre, suffix, rho, hrho, heq, hshort, hstart, hstop, hleft, hright⟩ :=
    exists_insertion_run left right bit
  have hconstant : ConstantOn
      (insertAt (listLetters (left ++ right)) left.length bit) pre.length rho bit := by
    rw [SingleEditScripts.insert_split, heq]
    exact constantOn_block pre suffix rho bit
  have hbound : pre.length + rho ≤ (left ++ right).length + 1 := by
    have hlength := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_replicate] at hlength ⊢
    omega
  have hrhoBound := insert_constant_length_le k (left ++ right).length
    (listLetters (left ++ right)) hx left.length bit
    (by simp only [List.length_append]; omega) pre.length rho bit hbound hconstant
  exact ⟨pre, suffix, rho, hrho, hrhoBound, heq, hshort, hstart, hstop, hleft, hright⟩
end DeletionCode.MaximalRuns
