-- Prove2me | solution 1 for Focil.compliant_includes_or_excused
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:55.180266+00:00
-- url     : https://prove2.me/submissions/693909fb-0e57-4eef-8ec3-337e75116bc8

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    {canAppend : Transaction → Block → Prop}
    {full : Block → Prop} {b : Block} {state : FocilState}
    {il : InclusionList} {tx : Transaction}
    (hCompl : FocilCompliant canAppend full b state)
    (hIl    : il ∈ state.stored_ils)
    (hConsidered : IsConsidered state il)
    (hTx    : tx ∈ il.transactions) :
    tx ∈ b.transactions ∨ ¬ canAppend tx b ∨ full b :=
  hCompl il hIl hConsidered tx hTx
end Focil
