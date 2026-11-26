-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_zero_of_edges_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:08.207342+00:00
-- url     : https://prove2.me/submissions/a4d737e3-fa24-49cb-96e7-6a6ed1354971

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_order_toFinset


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
    {I : ForestIndex V} (hI : I.edges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ = 0 := by
  rw [data.supportContribution_eq_sum_order_toFinset I ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ horder
    have hempty : e.val ∈ (∅ : Finset (Edge V)) := by
      rw [← hI, ← horder]
      exact List.mem_toFinset.mpr (by
        rw [List.mem_cons]
        exact Or.inl rfl)
    exact Finset.notMem_empty e.val hempty
end BKAR.Forest.ActiveTerminalBranchData
