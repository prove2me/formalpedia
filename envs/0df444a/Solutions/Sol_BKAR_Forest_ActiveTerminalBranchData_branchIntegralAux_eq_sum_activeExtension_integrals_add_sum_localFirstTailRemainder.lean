-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:25:54.873584+00:00
-- url     : https://prove2.me/submissions/ede68e9b-fe88-46a0-8083-1cc9958c37d7

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_localFirstTailRemainder_def
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_integrals_tail_partialDeriv
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_integrals_tail_partialDeriv
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
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t)) +
        Finset.sum F.activeEdges.attach
          (fun e => data.localFirstTailRemainder e top u es ρ) := by
  rw [data.branchIntegralAux_eq_sum_integrals_tail_partialDeriv]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [localFirstTailRemainder_def]
  rw [mixedPartialList_cons]
  ring
end BKAR.Forest.ActiveTerminalBranchData
