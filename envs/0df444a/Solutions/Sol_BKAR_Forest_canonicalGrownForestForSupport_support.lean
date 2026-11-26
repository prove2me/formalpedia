-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:35:05.035095+00:00
-- url     : https://prove2.me/submissions/81ce4e41-59b6-4999-8f5b-287237b5a496

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_support

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).support = I :=
  grownForestForSupportOrder_support choices I I.canonicalOrder
end BKAR.Forest
