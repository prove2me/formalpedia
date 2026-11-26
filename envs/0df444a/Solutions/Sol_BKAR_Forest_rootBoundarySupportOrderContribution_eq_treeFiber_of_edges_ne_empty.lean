-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:17:27.714673+00:00
-- url     : https://prove2.me/submissions/0508a8b9-7c13-4296-a060-0ec17a945cdd

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hI : I.edges ≠ ∅) :
    rootBoundarySupportOrderContribution choices ρ I order =
      boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
        I order ρ := by
  exact
    rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
      choices ρ I order (by
        intro hmarker
        exact hI hmarker.1)
end BKAR.Forest
