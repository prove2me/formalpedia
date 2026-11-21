-- Prove2me | solution 1 for Focil.focil_pos_derived_safety
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:39:36.013665+00:00
-- url     : https://prove2.me/submissions/888cc0eb-6615-4d3f-b542-f1e32b3c6313

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Safety
import Definitions.Def_Focil_StakeModel
import Theorems.Thm_Focil_focil_one_of_n_protection


set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    {s : StakeModel} (r : AttesterRun s)
    (b : Block) (tx : Transaction)
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ r.state.stored_ils
            ∧ IsConsidered r.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : r.canAppend tx b)
    (h_block_not_full: ¬ r.full b)
    (h_canonical     : IsCanonical r.toForkChoice b) :
    tx ∈ b.transactions :=
  focil_one_of_n_protection
    r.toForkChoice b tx
    h_listed_by_some_honest_member
    h_can_append h_block_not_full h_canonical
end Focil
