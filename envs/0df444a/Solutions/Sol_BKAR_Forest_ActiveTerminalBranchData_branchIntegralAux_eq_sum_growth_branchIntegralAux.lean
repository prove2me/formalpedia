-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_growth_branchIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:42.526428+00:00
-- url     : https://prove2.me/submissions/eb1753a2-065a-42e3-992b-a7d5bcf9425e

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => (data.growth e).branchIntegralAux top u ρ) :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
