-- Prove2me | solution 1 for BKAR.Forest.sum_localBoundarySupportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:02.67319+00:00
-- url     : https://prove2.me/submissions/2a57f3ae-1dbc-4d03-b950-de2b0f1d0341

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_sum_localBoundarySupportContribution
import Theorems.Thm_BKAR_Forest_localBoundarySupportContribution_eq_sum_supportOrderContribution
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
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum F.activeEdges.attach
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            localBoundarySupportOrderContribution choices F pref prefixTs top
              I order ρ)) := by
  rw [sum_localBoundarySupportContribution choices F pref prefixTs top ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [localBoundarySupportContribution_eq_sum_supportOrderContribution
    choices F pref prefixTs top hpref hnodup I ρ]
end BKAR.Forest
