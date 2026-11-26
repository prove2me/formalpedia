-- Prove2me | solution 1 for BKAR.Forest.localBoundarySupportContribution_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:00:02.593825+00:00
-- url     : https://prove2.me/submissions/d6bc5914-fa7b-4389-a616-4cb7def4f809

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
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportContribution choices F pref prefixTs top I ρ =
      Finset.sum
        (F.activeEdges.attach.filter
          (fun e => (choices F e).forest.support = I))
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) := by
  rw [localBoundarySupportContribution]
end BKAR.Forest
