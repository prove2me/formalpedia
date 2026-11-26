-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_terminal_orderedSectorSum_eq_sum_orderTails_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:10.278571+00:00
-- url     : https://prove2.me/submissions/70e5b816-496f-46b0-8426-35b3599f0f28

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_terminal_edges_nonempty_emptyStart
import Theorems.Thm_BKAR_Forest_orderedSectorSum_eq_sum_orderTails_of_edges_nonempty


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
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (data.growth e).terminal.orderedSectorSum ρ =
      Finset.sum (edgeSetOrderTails (data.growth e).terminal.edges)
        (fun x => (data.growth e).terminal.orderedContribution
          (x.1.val :: x.2) ρ) :=
  (data.growth e).terminal.orderedSectorSum_eq_sum_orderTails_of_edges_nonempty
    (data.growth_terminal_edges_nonempty_emptyStart e) ρ
end BKAR.Forest.ActiveTerminalBranchData
