-- Prove2me | solution 1 for BKAR.Forest.ChosenGrowth.branchIntegral_emptyStart_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:41.172746+00:00
-- url     : https://prove2.me/submissions/437eb117-78d3-4225-a66a-30234b596a1c

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_emptyStart_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {G : Forest V} {order : List (Edge V)}
namespace BKAR.Forest.ChosenGrowth
theorem _root_.solution
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    path.toOrderedGrowth.branchIntegral emptyParam ρ =
      G.orderedContribution order ρ :=
  path.toOrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution ρ
end BKAR.Forest.ChosenGrowth
