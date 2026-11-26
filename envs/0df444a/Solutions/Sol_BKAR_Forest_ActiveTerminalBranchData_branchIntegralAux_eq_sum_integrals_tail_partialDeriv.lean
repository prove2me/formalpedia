-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:25:01.743786+00:00
-- url     : https://prove2.me/submissions/0df7307d-65ef-444c-9b12-c57ec5f6dd50

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_integrals_tail_partialDeriv
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
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val ρ)) :=
  data.branchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv
    top u ρ
end BKAR.Forest.ActiveTerminalBranchData
