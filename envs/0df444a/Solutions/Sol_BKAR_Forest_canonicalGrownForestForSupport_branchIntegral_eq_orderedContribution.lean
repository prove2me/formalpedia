-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_branchIntegral_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:12.298543+00:00
-- url     : https://prove2.me/submissions/bc5585d1-f65a-4ebe-842c-cbcbb8da3067

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_emptyStart_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_ChosenGrowth_branchIntegral_emptyStart_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) :
  (canonicalGrownForestForSupport_orderedGrowth choices I).branchIntegral
        emptyParam ρ =
      (canonicalGrownForestForSupport choices I).orderedContribution
        I.canonicalOrder.val ρ :=
  OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution
    (canonicalGrownForestForSupport_orderedGrowth choices I) ρ
end BKAR.Forest
