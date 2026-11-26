-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_integral_branchIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:41.025351+00:00
-- url     : https://prove2.me/submissions/e89d7600-d603-4853-8b9c-5c20038f5232

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
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) :
    (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        I.canonicalOrder.val ρ =
      ∫ ts in orderedFinSimplex I.canonicalOrder.val.length,
        (canonicalGrownForestForSupport_orderedGrowth choices I).branchIntegrand
          emptyParam ρ (List.ofFn ts) :=
  OrderedGrowth.orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
    (canonicalGrownForestForSupport_orderedGrowth choices I) ρ
end BKAR.Forest
