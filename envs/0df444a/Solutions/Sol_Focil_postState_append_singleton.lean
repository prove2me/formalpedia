-- Prove2me | solution 1 for Focil.postState_append_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:52.891777+00:00
-- url     : https://prove2.me/submissions/d9124149-a839-4aa3-9b03-62c3a369e2a1

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_AccountState

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    (initial : AccountState) (txs : List Transaction)
    (tx : Transaction) :
    postState initial (txs ++ [tx]) =
    applyTx (postState initial txs) tx := by
  unfold postState
  simp [List.foldl_append]
end Focil
