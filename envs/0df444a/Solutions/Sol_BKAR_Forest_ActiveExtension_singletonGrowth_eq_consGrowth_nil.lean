-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.singletonGrowth_eq_consGrowth_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:18.673587+00:00
-- url     : https://prove2.me/submissions/f10a8509-8f55-4f04-a6e0-fd30fbe3d522

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution (h : ActiveExtension F e) :
    h.singletonGrowth = h.consGrowth (OrderedGrowth.nil h.forest) :=
  rfl
end BKAR.Forest.ActiveExtension
