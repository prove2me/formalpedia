-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.consGrowth_tailForest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:18.182113+00:00
-- url     : https://prove2.me/submissions/757d24de-cfe7-458c-82fa-0ecc41bbe4a9

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
    (h.consGrowth tail).tailForest = h.forest :=
  rfl
end BKAR.Forest.ActiveExtension
