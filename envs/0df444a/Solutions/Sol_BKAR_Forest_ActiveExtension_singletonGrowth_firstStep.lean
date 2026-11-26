-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.singletonGrowth_firstStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:36.224805+00:00
-- url     : https://prove2.me/submissions/cc1b3356-ea8b-4376-8c79-2504e90b1d38

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
    h.singletonGrowth.firstStep = h.extension :=
  rfl
end BKAR.Forest.ActiveExtension
