-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_branchPoint_eq_standardInterp_paramsOfOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:18.043035+00:00
-- url     : https://prove2.me/submissions/1a884872-6ec4-491d-9f75-f0d2af7e8309

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_def
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_emptyStart_eq_paramsOfOrder_of_length


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ts : List ℝ) (hlen : ts.length = I.canonicalOrder.val.length) :
    (canonicalGrownForestForSupport_orderedGrowth choices I).branchPoint
        emptyParam ts =
      (canonicalGrownForestForSupport choices I).standardInterp
        ((canonicalGrownForestForSupport choices I).paramsOfOrder
          I.canonicalOrder.val ts) := by
  rw [OrderedGrowth.branchPoint_def]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (canonicalGrownForestForSupport_orderedGrowth choices I) hlen]
end BKAR.Forest
