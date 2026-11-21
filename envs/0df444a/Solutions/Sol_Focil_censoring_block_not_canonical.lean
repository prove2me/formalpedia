-- Prove2me | solution 1 for Focil.censoring_block_not_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:39:12.349156+00:00
-- url     : https://prove2.me/submissions/a1f2554e-359d-4e3e-8003-0d62ef43ba73

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
    (fc : ForkChoice) (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ fc.state.stored_ils)
    (h_il_considered : IsConsidered fc.state il)
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_tx_excluded   : tx ∉ b.transactions) :
    ¬ IsCanonical fc b := by
  intro h_canonical
  exact h_tx_excluded
    (focil_censorship_resistance fc b il tx
      h_tx_in_il h_il_stored h_il_considered
      h_can_append h_block_not_full h_canonical)
end Focil
