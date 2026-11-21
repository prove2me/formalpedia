-- Prove2me | solution 1 for Focil.focil_concrete_safety
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:39:35.530417+00:00
-- url     : https://prove2.me/submissions/e61affe4-35fe-41aa-85b5-10ced5c1724f

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
import Definitions.Def_Focil_StakeModel
import Definitions.Def_Focil_AccountState
import Definitions.Def_Focil_EndToEnd
import Theorems.Thm_Focil_focil_one_of_n_protection


set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    (fc : ForkChoice) (b : Block) (tx : Transaction)
    (initial : AccountState)
    (h_canAppend_pin :
      fc.canAppend = fun tx' b' => canAppendToBlock initial b' tx')
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ fc.state.stored_ils
            ∧ IsConsidered fc.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : canAppendToBlock initial b tx)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by
  apply focil_one_of_n_protection fc b tx
    h_listed_by_some_honest_member ?_ h_block_not_full h_canonical
  rw [h_canAppend_pin]
  exact h_can_append
end Focil
