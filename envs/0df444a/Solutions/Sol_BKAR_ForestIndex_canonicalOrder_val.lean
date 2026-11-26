-- Prove2me | solution 1 for BKAR.ForestIndex.canonicalOrder_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:48.966829+00:00
-- url     : https://prove2.me/submissions/5d2afa79-f7f5-4ab0-a3b2-1325157f8e85

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.ForestIndex
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.ForestIndex
theorem _root_.solution (I : ForestIndex V) :
    I.canonicalOrder.val = I.edges.toList :=
  rfl
end BKAR.ForestIndex
