-- Prove2me | solution 1 for Focil.focil_concrete_pos_safety
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:39:58.988313+00:00
-- url     : https://prove2.me/submissions/61aae57c-2381-4e6f-a939-1e27dfc8dfbc

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
import Definitions.Def_Focil_StakeModel
import Definitions.Def_Focil_AccountState
import Definitions.Def_Focil_EndToEnd
import Theorems.Thm_Focil_focil_concrete_safety

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
    (h_canonical     : IsCanonical r.toForkChoice b) :
    tx ∈ b.transactions := by
  apply focil_concrete_safety r.toForkChoice b tx initial
    ?_ h_listed_by_some_honest_member h_can_append
    h_block_not_full h_canonical
  exact h_canAppend_pin
end Focil
