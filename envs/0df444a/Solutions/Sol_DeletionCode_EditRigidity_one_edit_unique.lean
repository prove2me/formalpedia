-- Prove2me | solution 1 for DeletionCode.EditRigidity.one_edit_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:50.934171+00:00
-- url     : https://prove2.me/submissions/5c9a0174-7d1f-4f42-9c43-6f427e70da4a

import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_TwoEditWindows
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_EditRigidity
import Theorems.Thm_DeletionCode_EditRigidity_shared_source_letters
import Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_origin_injective


set_option autoImplicit true
open DeletionCode DeletionCode.EditRigidity
open Windows HeaderRecovery SingleEditOrigins
namespace DeletionCode.EditRigidity
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n) :
    KUnique (e.word x) (e.outputLength n) (windowLength k - 1) := by
  intro a b ha hb hag
  obtain ⟨s, r, _, _, hsource⟩ := shared_source_letters hk x hx e e he he a b ha hb hag
  have h0 := hsource 0 (by omega)
  have hab := e.origin_injective h0.1 h0.2
  omega
end DeletionCode.EditRigidity
