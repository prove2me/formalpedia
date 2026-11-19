-- Prove2me | solution 1 for DeletionCode.PathMemory.pathInitialAgreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:14:32.689205+00:00
-- url     : https://prove2.me/submissions/b3665d17-c3c9-4287-9b9d-e3e7a6976e0a

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
import Theorems.Thm_DeletionCode_Windows_deletion_before


set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows
namespace DeletionCode.PathMemory
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters) :
    Agree (negativePath k h long) 0 (positivePath k h long) 0 (windowLength k - 1) := by
  cases ho : h.orientation with
  | deletion =>
    simp only [negativePath, positivePath, ho]
    intro i hi
    exact (deletion_before long (editOffset k) 0 (windowLength k - 1)
      (by unfold editOffset; omega) i hi).symm
  | insertion =>
    simp only [negativePath, positivePath, ho]
    exact deletion_before long (editOffset k) 0 (windowLength k - 1)
      (by unfold editOffset; omega)
end DeletionCode.PathMemory
