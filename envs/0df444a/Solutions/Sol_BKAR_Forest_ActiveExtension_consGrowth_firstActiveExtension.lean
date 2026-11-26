-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.consGrowth_firstActiveExtension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:17.460846+00:00
-- url     : https://prove2.me/submissions/f76c04a8-bf3b-4aa6-a3c2-e45aafd5ee96

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).firstActiveExtension = h :=
  rfl
end BKAR.Forest.ActiveExtension
