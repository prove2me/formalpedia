-- Prove2me | solution 1 for BKAR.Forest.localBoundarySupportOrderContribution_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:59:14.902798+00:00
-- url     : https://prove2.me/submissions/e0a2b201-325a-4c85-bea3-df9158d1ab22

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
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
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportOrderContribution choices F pref prefixTs top I order ρ =
      Finset.sum
        (F.activeEdges.attach.filter
          (fun e =>
            (choices F e).forest.support = I ∧
              pref ++ [e.val] = order))
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList order.reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder order
                  (prefixTs ++ ts))))) := by
  rw [localBoundarySupportOrderContribution]
end BKAR.Forest
