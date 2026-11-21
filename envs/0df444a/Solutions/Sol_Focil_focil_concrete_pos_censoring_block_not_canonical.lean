-- Prove2me | solution 1 for Focil.focil_concrete_pos_censoring_block_not_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:40:32.281772+00:00
-- url     : https://prove2.me/submissions/c7846972-2f51-4303-b99d-73e40cf1453a

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
import Definitions.Def_Focil_StakeModel
import Definitions.Def_Focil_AccountState
import Definitions.Def_Focil_EndToEnd
import Theorems.Thm_Focil_focil_concrete_pos_safety

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    {s : StakeModel} (r : AttesterRun s)
    (b : Block) (tx : Transaction)
    (initial : AccountState)
    (h_canAppend_pin :
      r.canAppend = fun tx' b' => canAppendToBlock initial b' tx')
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ r.state.stored_ils
            ∧ IsConsidered r.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : canAppendToBlock initial b tx)
    (h_block_not_full: ¬ r.full b)
    (h_tx_excluded   : tx ∉ b.transactions) :
    ¬ IsCanonical r.toForkChoice b := by
  intro h_canonical
  exact h_tx_excluded
    (focil_concrete_pos_safety r b tx initial
      h_canAppend_pin h_listed_by_some_honest_member
      h_can_append h_block_not_full h_canonical)
end Focil
