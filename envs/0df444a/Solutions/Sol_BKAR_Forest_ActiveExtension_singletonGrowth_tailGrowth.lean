-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.singletonGrowth_tailGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:38.274437+00:00
-- url     : https://prove2.me/submissions/33019256-2bf8-4737-b6b0-16172ffa2b34

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution (h : ActiveExtension F e) :
    h.singletonGrowth.tailGrowth = OrderedGrowth.nil h.forest :=
  rfl
end BKAR.Forest.ActiveExtension
