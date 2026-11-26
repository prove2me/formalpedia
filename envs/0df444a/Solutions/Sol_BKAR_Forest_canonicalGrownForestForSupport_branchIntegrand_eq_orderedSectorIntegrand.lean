-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_branchIntegrand_eq_orderedSectorIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:19.792905+00:00
-- url     : https://prove2.me/submissions/6b2e8d32-55d8-4919-9b49-7f96e9b2d465

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def_standardInterp
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_emptyStart_eq_paramsOfOrder_of_length


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (hlen : ts.length = I.canonicalOrder.val.length) :
    (canonicalGrownForestForSupport_orderedGrowth choices I).branchIntegrand
        emptyParam ρ ts =
      mixedPartialList I.canonicalOrder.val.reverse ρ
        ((canonicalGrownForestForSupport choices I).standardInterp
          ((canonicalGrownForestForSupport choices I).paramsOfOrder
            I.canonicalOrder.val ts)) := by
  rw [OrderedGrowth.branchIntegrand_def_standardInterp]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (canonicalGrownForestForSupport_orderedGrowth choices I) hlen]
end BKAR.Forest
