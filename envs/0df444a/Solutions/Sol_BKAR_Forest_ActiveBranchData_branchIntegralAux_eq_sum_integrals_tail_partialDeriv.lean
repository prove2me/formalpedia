-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:17.146768+00:00
-- url     : https://prove2.me/submissions/fbb2e15a-b16f-4923-ba24-981b4c4aaada

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution
    (data : ActiveBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val ρ)) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (data.extension e).consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    (data.tail e) top u ρ
end BKAR.Forest.ActiveBranchData
