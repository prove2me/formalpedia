-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_nil_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:48.941368+00:00
-- url     : https://prove2.me/submissions/cc5760dd-6aa2-476b-8ca5-044532dcd437

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_eq
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_def


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
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I [] ρ = 0 := by
  rw [data.supportOrderContribution_def I [] ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    have horder := h.2
    rw [data.growthOrder_eq e] at horder
    cases horder
end BKAR.Forest.ActiveTerminalBranchData
