-- Prove2me | solution 1 for Focil.noncompliant_block_not_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:38:37.016005+00:00
-- url     : https://prove2.me/submissions/cecd03c6-8790-4a21-8f68-0090d2107ff9

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Theorems.Thm_Focil_canonical_implies_compliant

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    (fc : ForkChoice) (b : Block)
    (h_noncompliant : ¬ FocilCompliant fc.canAppend fc.full b fc.state) :
    ¬ IsCanonical fc b := by
  intro h_canon
  exact h_noncompliant
    (canonical_implies_compliant fc b h_canon)
end Focil
