-- Prove2me | solution 1 for DeciSigma1.Semantics.isRegular_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:56.91882+00:00
-- url     : https://prove2.me/submissions/6ab0a552-7980-462f-9bf0-e3b4bc631bf5

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Theorems.Thm_DeciSigma1_Semantics_residual_append

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Automata
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution {F : Set (Language n)} (hf : F.Finite) {L : Language n}
    (hl : L ∈ F) (hc : ∀ A ∈ F, ∀ c, residual A [c] ∈ F) : IsRegular L := by
  apply hf.subset
  rintro _ ⟨u,rfl⟩
  induction u using List.reverseRecOn with
  | nil => exact hl
  | append_singleton u c ih => rw [residual_append]; exact hc _ ih c
end DeciSigma1.Semantics
