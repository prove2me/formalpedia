-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:54:06.857689+00:00
-- url     : https://prove2.me/submissions/005ceccd-7d98-4911-8d85-38e4e415196d

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution

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
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  rw [supportContribution]
end BKAR.Forest.ActiveTerminalBranchData
