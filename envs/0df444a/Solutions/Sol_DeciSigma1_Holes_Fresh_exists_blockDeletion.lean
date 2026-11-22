-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.exists_blockDeletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:07.823509+00:00
-- url     : https://prove2.me/submissions/f91fe758-43eb-46c0-90d1-39ec5a324485

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_lowerLevelTypes_mem_choices
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_lowerLevelTypeChoices_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_labels_eq_of_jointLabel
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
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (ht : t ≤ k * Fintype.card S + 1) (e : Edge W t)
    (hlong : edgeLengthBound k (Fintype.card S) < e.endDepth - e.startDepth) : Nonempty
        (BlockDeletion T W t) := by
  classical
  let C := (lowerLevelTypeChoices W t) ×ˢ (univ : Finset (S → S))
  have hcard : C.card ≤ (k + 1) ^ (k * Fintype.card S + 1) *
      Fintype.card S ^ Fintype.card S := by
    calc
      C.card = (lowerLevelTypeChoices W t).card * Fintype.card S ^ Fintype.card S := by
        simp [C]
      _ ≤ (k + 1)^t * Fintype.card S ^ Fintype.card S :=
        Nat.mul_le_mul_right _ (card_lowerLevelTypeChoices_le W t)
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) ht)
  let D :=
      Icc (e.startDepth + deletionMargin k (Fintype.card S))
          (e.endDepth - deletionMargin k (Fintype.card S))
  have hlt : C.card < D.card := by
    change C.card <
        (Icc (e.startDepth + deletionMargin k (Fintype.card S)) (e.endDepth - deletionMargin k
            (Fintype.card S))).card
    rw [Nat.card_Icc]
    unfold edgeLengthBound at hlong
    omega
  have hmap : ∀ p ∈ D, jointLabel T e p ∈ C := by
    intro p _
    exact mem_product.mpr ⟨lowerLevelTypes_mem_choices _ _ _, mem_univ _⟩
  obtain ⟨i, hi, j, hj, hneij, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt hmap
  simp only [D, mem_Icc] at hi hj
  have hM : 0 < deletionMargin k (Fintype.card S) := by unfold deletionMargin; omega
  have hb : deletionMargin k (Fintype.card S) ≤ e.endDepth := by
    unfold edgeLengthBound at hlong; omega
  rcases lt_or_gt_of_ne hneij with hij | hji
  · exact ⟨⟨e, i, j, hi.1, hij, by omega, fun o ho hth =>
      labels_eq_of_jointLabel hfr e (by omega) (by omega) (by omega)
          (by omega) heq.symm ho hth⟩⟩
  · exact ⟨⟨e, j, i, hj.1, hji, by omega, fun o ho hth =>
      labels_eq_of_jointLabel hfr e (by omega) (by omega) (by omega) (by omega) heq ho hth⟩⟩
end DeciSigma1.Holes.Fresh
