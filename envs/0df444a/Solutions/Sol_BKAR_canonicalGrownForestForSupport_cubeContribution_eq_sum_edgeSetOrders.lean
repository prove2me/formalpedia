-- Prove2me | solution 1 for BKAR.canonicalGrownForestForSupport_cubeContribution_eq_sum_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:37:59.154997+00:00
-- url     : https://prove2.me/submissions/de55a95e-eb1f-47c7-9c83-69b8fec7c825

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
import Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport


set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
theorem _root_.solution
    (choices : Forest.ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ =
      Finset.sum (Forest.edgeSetOrders I.edges)
        (fun order =>
          (Forest.canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
            order ρ) := by
  exact
    (Forest.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport
      choices I ρ hρ).symm
end BKAR
