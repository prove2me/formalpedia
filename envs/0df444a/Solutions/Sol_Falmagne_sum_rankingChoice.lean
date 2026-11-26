-- Prove2me | solution 1 for Falmagne.sum_rankingChoice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:06.704804+00:00
-- url     : https://prove2.me/submissions/49d8c887-6e9e-4b94-94e4-cd029a194149

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Basic
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_chosen_unique
public import Theorems.Thm_Falmagne_exists_chosen
attribute [local simp] Falmagne.mem_lowerContour

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x y : X}
namespace Falmagne
theorem _root_.solution (hl : IsRanking l) (hA : A.Nonempty) :
    ∑ x ∈ A, rankingChoice l A x = 1 := by
  obtain ⟨x, hx, hchosen⟩ := exists_chosen hl hA
  rw [Finset.sum_eq_single x]
  · simp [rankingChoice, hx, hchosen]
  · intro y hy hyx
    by_cases h : y ∈ A ∧ A ⊆ lowerContour l y
    · exact (hyx (chosen_unique hl h ⟨hx, hchosen⟩)).elim
    · simp [rankingChoice, h]
  · intro h
    exact (h hx).elim
end Falmagne
