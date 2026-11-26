-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_support_edges_filter_tail_branchIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:14.388079+00:00
-- url     : https://prove2.me/submissions/56e7c896-b343-4dc6-8caa-028fdc7db51b

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_supportContribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_support_edges_filter_tail_branchIntegralAux
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
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I =>
          Finset.sum
            (I.edges.attach.filter
              (fun e =>
                (data.tail (emptyActiveEdge e.val)).order ∈
                  edgeSetOrders (I.edges.erase e.val)))
            (fun e => ∫ t in 0..(1 : ℝ),
              (data.tail (emptyActiveEdge e.val)).branchIntegralAux t
                ((data.extension (emptyActiveEdge e.val)).extension.extendParam
                  emptyParam t)
                (partialDeriv e.val ρ))) := by
  rw [data.branchIntegral_empty_eq_sum_supportContribution ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [data.supportContribution_eq_sum_support_edges_filter_tail_branchIntegralAux
    I ρ]
end BKAR.Forest.ActiveTerminalBranchData
