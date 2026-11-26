-- Prove2me | solution 1 for BKAR.Forest.integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:44.758102+00:00
-- url     : https://prove2.me/submissions/d6efe3c3-2d3d-49b5-a98a-a815875e1e5f

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_orderedSimplexIntegral_singleton


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ)
    (hterm :
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ := by
  have hcard :
      (choices (Forest.empty V) e).forest.activeEdges.card = 0 := by
    rw [hterm, Finset.card_empty]
  rw [hcard]
  change
    (∫ t in 0..(1 : ℝ),
        mixedPartialList [e.val].reverse ρ
          ((choices (Forest.empty V) e).forest.standardInterp
            ((choices (Forest.empty V) e).forest.paramsOfOrder [e.val] [t]))) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ
  rw [orderedContribution, orderedSimplexIntegral_singleton]
end BKAR.Forest
