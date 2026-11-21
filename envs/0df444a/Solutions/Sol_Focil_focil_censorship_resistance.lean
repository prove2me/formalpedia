-- Prove2me | solution 1 for Focil.focil_censorship_resistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:38:36.467989+00:00
-- url     : https://prove2.me/submissions/c5ebb357-d4a1-4c69-b53a-98a810e8a12b

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
import Theorems.Thm_Focil_canonical_implies_compliant


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
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by
  have hCompl : FocilCompliant fc.canAppend fc.full b fc.state :=
    canonical_implies_compliant fc b h_canonical
  have h := hCompl il h_il_stored h_il_considered tx h_tx_in_il
  cases h with
  | inl h_in => exact h_in
  | inr h_rest =>
    cases h_rest with
    | inl h_not_appendable => exact (h_not_appendable h_can_append).elim
    | inr h_full           => exact (h_block_not_full h_full).elim
end Focil
