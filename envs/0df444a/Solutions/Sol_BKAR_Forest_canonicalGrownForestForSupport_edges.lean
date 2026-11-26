-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:24.305949+00:00
-- url     : https://prove2.me/submissions/123e6b83-b938-4a28-9b0d-41f6eb34bae9

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_edges

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).edges = I.edges :=
  grownForestForSupportOrder_edges choices I I.canonicalOrder
end BKAR.Forest
