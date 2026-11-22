-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.mem_deletedPositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:16.880881+00:00
-- url     : https://prove2.me/submissions/b09faaa3-39a4-476b-b509-90c489095bbc

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
variable (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ)
variable {W ρ N x}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {l : Fin k} {p : ℕ} : p ∈ deletedPositions W ρ N x l ↔
    ∃ P ∈ piecesOf W ρ, P.coordinate = l ∧ P.start + Periodic.boundaryMargin N ρ.length ≤ p ∧
      p < P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x P := by
  simp only
      [deletedPositions, pieceDeletionSites, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨P, ⟨hP, hl⟩, h⟩; exact ⟨P, hP, hl, h⟩
  · rintro ⟨P, hP, hl, h⟩; exact ⟨P, ⟨hP, hl⟩, h⟩
end DeciSigma1.Holes.Periodic
