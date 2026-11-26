-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_activeExtension_integrals_of_forall_tail_order_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:22.62628+00:00
-- url     : https://prove2.me/submissions/9a861f05-9463-4fea-bca2-b189f96827fa

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
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
    (htail : ∀ e : {e // e ∈ F.activeEdges}, (data.tail e).order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t)) := by
  rw [data.branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
    top u es ρ]
  have hzero :
      Finset.sum F.activeEdges.attach
          (fun e => data.localFirstTailRemainder e top u es ρ) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact data.localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
      e (htail e) top u es ρ
  rw [hzero, add_zero]
end BKAR.Forest.ActiveTerminalBranchData
