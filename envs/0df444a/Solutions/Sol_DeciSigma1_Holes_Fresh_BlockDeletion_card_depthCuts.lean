-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.card_depthCuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:48.878599+00:00
-- url     : https://prove2.me/submissions/848fd53b-cebe-4ff3-b15d-5e0d1e440ecb

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt
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
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    {D : ℕ} (hD : D ≤ lowerBlockCount W t o) {X : Finset ℕ} (hX : ∀ d ≤ D, depthCut W t o d ∈ X) :
    D + 1 ≤ X.card := by
  have hinj : Set.InjOn (depthCut W t o) (range (D + 1)) := by
    intro d hd d' hd' he
    simp only [coe_range, Set.mem_Iio] at hd hd'
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact absurd he (depthCut_lt_of_lt ho h (by omega)).ne'
    · exact absurd he (depthCut_lt_of_lt ho h (by omega)).ne
  calc D + 1 = ((range (D + 1)).image (depthCut W t o)).card := by
        rw [card_image_of_injOn hinj, card_range]
    _ ≤ X.card := card_le_card (fun p hp => by
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
        exact hX d (by simp at hd; omega))
end DeciSigma1.Holes.Fresh.BlockDeletion
