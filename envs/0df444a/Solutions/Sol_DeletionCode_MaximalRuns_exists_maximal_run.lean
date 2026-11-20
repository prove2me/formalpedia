-- Prove2me | solution 1 for DeletionCode.MaximalRuns.exists_maximal_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:18.150044+00:00
-- url     : https://prove2.me/submissions/72530621-0999-45c7-8953-b5df7774247b

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_exists_head_run
section
namespace DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
private theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all
end DeletionCode.MaximalRuns
end

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (word : List Bool) (pos : ℕ) (hpos : pos < word.length) :
    ∃ (pre suffix : List Bool) (rho : ℕ) (bit : Bool),
      0 < rho ∧ word = pre ++ List.replicate rho bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  induction word generalizing pos with
  | nil => simp at hpos
  | cons head tail ih =>
    cases pos with
    | zero =>
      obtain ⟨rho, suffix, hrho, heq, hright⟩ := exists_head_run head tail
      exact ⟨[], suffix, rho, head, hrho, by simpa using heq,
        by simp, by simpa using hrho, Or.inl rfl, hright⟩
    | succ pos =>
      have htail : pos < tail.length := by
        simp only [List.length_cons] at hpos
        omega
      obtain ⟨pre, suffix, rho, bit, hrho, heq, hstart, hstop, hleft, hright⟩ :=
        ih pos htail
      cases pre with
      | nil =>
        simp only [List.nil_append, List.length_nil, Nat.zero_add] at heq hstart hstop
        by_cases hhead : head = bit
        · subst head
          refine ⟨[], suffix, rho + 1, bit, by omega, ?_, by simp,
            by simpa using Nat.succ_lt_succ hstop, Or.inl rfl, hright⟩
          simpa only [List.nil_append, List.replicate_succ, List.cons_append]
            using congrArg (List.cons bit) heq
        · refine ⟨[head], suffix, rho, bit, hrho, ?_, by simp,
            by simp only [List.length_cons, List.length_nil]; omega, Or.inr ?_, hright⟩
          · simpa only [List.cons_append, List.nil_append]
              using congrArg (List.cons head) heq
          · change some head = some (!bit)
            exact congrArg some (bool_eq_not_of_ne hhead)
      | cons first rest =>
        refine ⟨head :: first :: rest, suffix, rho, bit, hrho, ?_, ?_, ?_, ?_, hright⟩
        · simpa only [List.cons_append] using congrArg (List.cons head) heq
        · simp only [List.length_cons] at hstart ⊢
          omega
        · simp only [List.length_cons] at hstop ⊢
          omega
        · rcases hleft with hnil | hlast
          · simp at hnil
          · exact Or.inr (by simpa only [List.getLast?_cons_cons] using hlast)
end DeletionCode.MaximalRuns
