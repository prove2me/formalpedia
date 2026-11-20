-- Prove2me | solution 1 for DeletionCode.BubbleLocalSpectrum.shared_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:22.893497+00:00
-- url     : https://prove2.me/submissions/4b719ddd-bcc5-4243-8577-67ca7523b302

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_delete_longWord


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.BubbleLocalSpectrum
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) 0 (listLetters bubble.shortWord) 0
      (windowLength k - 1) := by
  rw [← bubble.delete_longWord]
  intro i hi
  simp only [Nat.zero_add, deleteAt, editOffset, if_pos hi]
end DeletionCode.BubbleLocalSpectrum
