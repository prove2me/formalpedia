-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.anchorCount_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:23.182814+00:00
-- url     : https://prove2.me/submissions/091d8c5b-472b-4726-9c5f-0fa6ef0e8abe

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
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
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
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
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) :
    anchorCount A (base + lo) (base + n) = anchorCount Q lo n := by
  unfold anchorCount
  have himg : (Q.filter (fun p => lo < p ∧ p ≤ n)).image (base + ·) =
      A.filter (fun p => base + lo < p ∧ p ≤ base + n) := by
    ext p
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, h1, h2⟩, rfl⟩
      exact ⟨(hag q (by omega) h2).mpr hq, by omega, by omega⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨p - base, ⟨(hag _ (by omega) (by omega)).mp ?_, by omega, by omega⟩, by omega⟩
      rwa [Nat.add_sub_cancel' (by omega)]
  rw [← himg, card_image_of_injective _ (add_right_injective base)]
end DeciSigma1.Holes.Fresh
