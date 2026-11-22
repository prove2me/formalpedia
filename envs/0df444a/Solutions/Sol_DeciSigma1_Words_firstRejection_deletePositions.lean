-- Prove2me | solution 1 for DeciSigma1.Words.firstRejection_deletePositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:12.555947+00:00
-- url     : https://prove2.me/submissions/f35bdef7-3067-4b55-8d8e-fd97b95fdf28

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_le_greatestPreimage_iff
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_mono
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_length
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_rejected_iff_firstRejection_le
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_rejected_of_firstRejection_le


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (M : StructuralReader α S k) {W U : Fin k → List α}
    {i : Fin k} (hW : M.Eligible W i) (hU : U i = deletePositions (W i) D)
    (hD : (W i).length ∉ D)
    (hrun : ∀ a, M.runPrefix U i a = M.runPrefix W i (greatestPreimage D a)) :
    M.firstRejection U i = retainedCount D (M.firstRejection W i) := by
  have hend : greatestPreimage D (U i).length =
      (W i).length := by rw [hU]; exact greatestPreimage_length _ hD
  have hlen : (U i).length = retainedCount D (W i).length := by rw [hU, length_deletePositions]
  have hUe : M.Eligible U i := by
    refine ⟨fun a _ => by rw [hrun]; exact hW.runPrefix_ne _, ?_⟩
    have h2 := hW.2
    unfold Table.endState at h2 ⊢
    rwa [hrun, hend]
  have hJ := StructuralReader.firstRejection_spec hW
  have hJ' := StructuralReader.firstRejection_spec hUe
  have hle : retainedCount D (M.firstRejection W i) ≤ (U i).length :=
    hlen ▸ retainedCount_mono hJ.1
  apply le_antisymm
  · refine (StructuralReader.rejected_iff_firstRejection_le hUe hle).mp ?_
    rw [hrun]
    exact StructuralReader.rejected_of_firstRejection_le hW (le_greatestPreimage_iff.mpr le_rfl)
      (hend ▸ greatestPreimage_mono hle)
  · have hr : M.rejected (M.runPrefix W i (greatestPreimage D (M.firstRejection U i))) = true := by
      rw [← hrun]; exact hJ'.2.1
    exact le_greatestPreimage_iff.mp ((StructuralReader.rejected_iff_firstRejection_le hW
      (hend ▸ greatestPreimage_mono hJ'.1)).mp hr)
end DeciSigma1.Words
