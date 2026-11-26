-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:08.276924+00:00
-- url     : https://prove2.me/submissions/91ed1fbd-4adf-4df4-a121-a86dede8aaf6

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
import Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplex


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
      (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        order.val ρ := by
  rw [grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    choices I order ρ]
  rw [canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    choices I order ρ]
  apply setIntegral_congr_fun (measurableSet_orderedFinSimplex order.val.length)
  intro ts _hts
  exact
    grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
      choices I order ρ ts
end BKAR.Forest
