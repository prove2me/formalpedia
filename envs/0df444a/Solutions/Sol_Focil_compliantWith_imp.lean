-- Prove2me | solution 1 for Focil.compliantWith_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:38:12.303184+00:00
-- url     : https://prove2.me/submissions/da660f66-24ce-4015-a9a8-6f7bc1e2433d

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_Helpers

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    {canAppend : Transaction → Block → Prop}
    {full : Block → Prop} {b : Block} {il : InclusionList}
    {tx : Transaction}
    (h : CompliantWith canAppend full b il)
    (htx : tx ∈ il.transactions) :
    tx ∈ b.transactions ∨ ¬ canAppend tx b ∨ full b :=
  h tx htx
end Focil
