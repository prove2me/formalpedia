-- Prove2me | solution 1 for DeletionCode.EditLocality.local_output_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:27.606139+00:00
-- url     : https://prove2.me/submissions/38854998-2640-479c-a6c0-bb436ea61dc0

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality

set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins
namespace DeletionCode.EditLocality
theorem _root_.solution (e : Edit) (start len n : ℕ)
    (he : Inside e start len) (hbound : start + len ≤ n) :
    start + e.outputLength len ≤ e.outputLength n := by
  cases e <;> simp only [Inside, Edit.outputLength] at he ⊢ <;> omega
end DeletionCode.EditLocality
