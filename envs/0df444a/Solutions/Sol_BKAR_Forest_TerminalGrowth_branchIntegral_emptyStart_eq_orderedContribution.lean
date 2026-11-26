-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegral_emptyStart_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:26:04.061856+00:00
-- url     : https://prove2.me/submissions/f024b16b-046a-4c68-a33f-f2c26fea6b5b

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_emptyStart_eq_paramsOfOrder_of_length
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
import Theorems.Thm_BKAR_orderedSimplexIntegral_congr_of_length


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth (Forest.empty V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      data.terminal.orderedContribution data.order ρ := by
  rw [branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp]
  rw [orderedContribution]
  exact orderedSimplexIntegral_congr_of_length (fun ts hlen => by
    rw [data.growth.params_emptyStart_eq_paramsOfOrder_of_length hlen])
end BKAR.Forest.TerminalGrowth
