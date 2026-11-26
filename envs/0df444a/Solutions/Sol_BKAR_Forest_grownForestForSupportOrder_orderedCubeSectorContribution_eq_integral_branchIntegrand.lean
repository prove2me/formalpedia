-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_integral_branchIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:21.851886+00:00
-- url     : https://prove2.me/submissions/f4b0223b-7e5f-4272-a3db-ffce6ea756f1

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_Forest_OrderedGrowth_orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        (grownForestForSupportOrder_orderedGrowth choices I order).branchIntegrand
          emptyParam ρ (List.ofFn ts) :=
  OrderedGrowth.orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
    (grownForestForSupportOrder_orderedGrowth choices I order) ρ
end BKAR.Forest
