-- Prove2me | solution 1 for BKAR.Forest.integral_allBranchesBoundaryExpansion_singleton_eq_prefixed_orderedSimplexIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:34.086259+00:00
-- url     : https://prove2.me/submissions/dfe3a2d8-5e72-47fc-9b9b-f2a84a2317b0

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (G : Forest V) (e : Edge V)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hG : G.activeEdges = ∅) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices G.activeEdges.card
          G (pref ++ [e]) (prefixTs ++ [t]) t ρ) =
      orderedSimplexIntegralAux top [e]
        (fun ts => mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ ts)))) := by
  have hcard : G.activeEdges.card = 0 := by
    rw [hG, Finset.card_empty]
  rw [hcard]
  rfl
end BKAR.Forest
