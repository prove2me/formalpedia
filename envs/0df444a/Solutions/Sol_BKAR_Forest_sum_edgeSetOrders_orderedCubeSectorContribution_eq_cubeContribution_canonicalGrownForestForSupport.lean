-- Prove2me | solution 1 for BKAR.Forest.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:23.312286+00:00
-- url     : https://prove2.me/submissions/58f5a5ef-e2da-47cd-b595-523bc998443d

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
import Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_of_edges_eq
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Finset.sum (edgeSetOrders I.edges)
      (fun order =>
        (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
          order ρ) =
      (canonicalGrownForestForSupport choices I).cubeContribution ρ :=
  (canonicalGrownForestForSupport choices I)
    |>.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_of_edges_eq
      I ρ hρ (canonicalGrownForestForSupport_edges choices I)
end BKAR.Forest
