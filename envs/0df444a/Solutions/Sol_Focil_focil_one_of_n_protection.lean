-- Prove2me | solution 1 for Focil.focil_one_of_n_protection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:39:11.756819+00:00
-- url     : https://prove2.me/submissions/d50e67d6-cfb1-4028-9a49-1ef8338be5b0

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
import Theorems.Thm_Focil_focil_censorship_resistance

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    (fc : ForkChoice) (b : Block) (tx : Transaction)
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ fc.state.stored_ils
            ∧ IsConsidered fc.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by
  obtain ⟨il, h_il_stored, h_il_considered, h_tx_in_il⟩ :=
    h_listed_by_some_honest_member
  exact focil_censorship_resistance fc b il tx
    h_tx_in_il h_il_stored h_il_considered
    h_can_append h_block_not_full h_canonical
end Focil
