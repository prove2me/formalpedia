-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.localFirstTailRemainder_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:13:15.372074+00:00
-- url     : https://prove2.me/submissions/5dffde52-b4be-42ca-8326-8dc7c0722ed7

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.localFirstTailRemainder e top u es ρ =
      (∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val (mixedPartialList es ρ))) -
        ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t) :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
