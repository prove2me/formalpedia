-- Prove2me | solution 1 for BKAR.Forest.sum_localBoundarySupportContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:22.383401+00:00
-- url     : https://prove2.me/submissions/bf8d9c51-f5ce-4892-bc6d-8888ed938b04

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_localBoundarySupportContribution_def
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum F.activeEdges.attach
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I =>
          localBoundarySupportContribution choices F pref prefixTs top I ρ) := by
  classical
  have hmap :
      ∀ e ∈ F.activeEdges.attach,
        (choices F e).forest.support ∈
          (Finset.univ : Finset (ForestIndex V)) := by
    intro e _
    exact Finset.mem_univ _
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := F.activeEdges.attach)
      (t := (Finset.univ : Finset (ForestIndex V)))
      (g := fun e => (choices F e).forest.support)
      hmap
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ ts)))))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro I _
  rw [localBoundarySupportContribution_def choices F pref prefixTs top I ρ]
end BKAR.Forest
