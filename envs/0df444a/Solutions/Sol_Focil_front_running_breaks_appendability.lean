-- Prove2me | solution 1 for Focil.front_running_breaks_appendability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:38:19.881909+00:00
-- url     : https://prove2.me/submissions/b0a6af30-6890-4338-85a4-91dbb870ec31

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_AccountState
import Theorems.Thm_Focil_postState_append_singleton

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    (initial : AccountState)
    (b : Block)
    (tx_il tx_evil : Transaction)
    (h_same_sender    : tx_evil.sender = tx_il.sender)
    (h_il_appendable  : canAppendToBlock initial b tx_il)
    (h_evil_appendable: canAppendToBlock initial b tx_evil) :
    ¬ canAppendToBlock initial
        { b with transactions := b.transactions ++ [tx_evil] }
        tx_il := by
  intro h_app
  unfold canAppendToBlock canAppendNonce at h_app
  rw [show ({ b with transactions := b.transactions ++ [tx_evil] }
           : Block).transactions = b.transactions ++ [tx_evil] from rfl,
      postState_append_singleton] at h_app
  unfold applyTx at h_app
  have h_cond_left : tx_il.sender = tx_evil.sender := h_same_sender.symm
  have h_cond_right :
      tx_evil.nonce = postState initial b.transactions tx_evil.sender :=
    h_evil_appendable
  rw [if_pos ⟨h_cond_left, h_cond_right⟩] at h_app
  have h_il_nonce :
      tx_il.nonce = postState initial b.transactions tx_il.sender :=
    h_il_appendable
  rw [h_il_nonce] at h_app
  exact Nat.succ_ne_self _ h_app.symm
end Focil
