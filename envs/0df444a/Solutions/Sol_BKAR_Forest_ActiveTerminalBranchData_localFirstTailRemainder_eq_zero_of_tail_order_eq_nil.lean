-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:28.945422+00:00
-- url     : https://prove2.me/submissions/988fd837-9fbd-4235-b22c-643229664766

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_localFirstTailRemainder_def
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_extension_activeEdges_eq_empty_of_tail_order_eq_nil
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_standardInterp_of_order_eq_nil
import Theorems.Thm_BKAR_Forest_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
import Theorems.Thm_BKAR_mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons



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
    (htail : (data.tail e).order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.localFirstTailRemainder e top u es ρ = 0 := by
  rw [localFirstTailRemainder_def]
  have htailIntegral :
      (∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val (mixedPartialList es ρ))) =
        ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t) := by
    apply intervalIntegral.integral_congr
    intro t _
    change (data.tail e).branchIntegralAux t
        ((data.extension e).extension.extendParam u t)
        (partialDeriv e.val (mixedPartialList es ρ)) =
      mixedPartialList (e.val :: es) ρ
        ((data.extension e).forest.interpWithFill
          ((data.extension e).extension.extendParam u t) t)
    rw [(data.tail e).branchIntegralAux_eq_standardInterp_of_order_eq_nil
      htail t
      ((data.extension e).extension.extendParam u t)
      (partialDeriv e.val (mixedPartialList es ρ))]
    rw [mixedPartialList_cons]
    rw [← (data.extension e).forest.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
      ((data.extension e).extension.extendParam u t) t
      (data.extension_activeEdges_eq_empty_of_tail_order_eq_nil e htail)]
  rw [htailIntegral, sub_self]
end BKAR.Forest.ActiveTerminalBranchData
