-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.rebuild_positive_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:12:00.129291+00:00
-- url     : https://prove2.me/submissions/0467acc0-3d6e-4e7f-b307-c712d9449b07

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_Windows_insert_delete


set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (hbit : long (editOffset k) = h.bit) :
    rebuildPositive k h (negativePath k h long) = positivePath k h long := by
  cases ho : h.orientation with
  | deletion => simp only [rebuildPositive, negativePath, positivePath, ho]
  | insertion =>
    simp only [rebuildPositive, negativePath, positivePath, ho]
    rw [← hbit]
    exact insert_delete long (editOffset k)
end DeletionCode.HeaderRecovery
