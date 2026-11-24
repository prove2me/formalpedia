-- Prove2me | solution 1 for FongoSync.fold_keep_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:54.518654+00:00
-- url     : https://prove2.me/submissions/776db197-594e-4419-91b7-7e52565ff510

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_fold_keep_spec
import Theorems.Thm_FongoSync_fold_keep_none

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution (l₁ l₂ : List E) (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (inj : KeyInj key l₁) :
    l₁.foldl (keep cmp key) none = l₂.foldl (keep cmp key) none := by
  cases h₁ : l₁.foldl (keep cmp key) none with
  | none =>
    have ⟨_, e₁⟩ := (fold_keep_none l₁ none).mp h₁
    have e₂ : l₂ = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
      have := (same x).mpr hx; simp_all
    simp [e₂]
  | some m₁ =>
    cases h₂ : l₂.foldl (keep cmp key) none with
    | none =>
      have ⟨_, e₂⟩ := (fold_keep_none l₂ none).mp h₂
      have e₁ : l₁ = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
        have := (same x).mp hx; simp_all
      simp [e₁] at h₁
    | some m₂ =>
      have ⟨mem₁, all₁, _⟩ := fold_keep_spec l₁ none m₁ h₁
      have ⟨mem₂, all₂, _⟩ := fold_keep_spec l₂ none m₂ h₂
      simp only [reduceCtorEq, false_or] at mem₁ mem₂
      have mem₂' := (same m₂).mpr mem₂
      have le₁ := all₁ m₂ mem₂'
      have le₂ := all₂ m₁ ((same m₁).mp mem₁)
      have heq := OrientedCmp.isLE_antisymm le₁ le₂
      rw [inj m₂ mem₂' m₁ mem₁ (LawfulEqCmp.eq_of_compare heq)]
end FongoSync
