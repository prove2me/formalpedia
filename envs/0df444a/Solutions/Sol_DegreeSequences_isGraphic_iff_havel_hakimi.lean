-- Prove2me | solution 1 for DegreeSequences.isGraphic_iff_havel_hakimi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:00:28.473644+00:00
-- url     : https://prove2.me/submissions/4cc195f9-f19d-4630-be14-7719a0b16b80

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_isGraphic_of_havelHakimi
public import Theorems.Thm_DegreeSequences_havelHakimi_of_isGraphic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧
      IsGraphic (havelHakimi d) := by
  exact ⟨havelHakimi_of_isGraphic d hd,
    fun ⟨h0, hpos, hH⟩ => isGraphic_of_havelHakimi d h0 hpos hH⟩
end DegreeSequences
