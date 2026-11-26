-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegralAux_mixedPartialList_eq_orderedSimplexIntegralAux_paramsOfOrder_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:13.133+00:00
-- url     : https://prove2.me/submissions/64173459-948b-437d-b0b0-0b1977e37a34

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_eq_paramsOfOrder_append_of_length
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
import Theorems.Thm_BKAR_mixedPartialList_append
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr_of_length


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth F) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top (F.paramsOfOrder pref prefixTs)
        (mixedPartialList pref.reverse ρ) =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList (pref ++ data.order).reverse ρ
          (data.terminal.standardInterp
            (data.terminal.paramsOfOrder (pref ++ data.order)
              (prefixTs ++ ts)))) := by
  rw [data.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp]
  exact orderedSimplexIntegralAux_congr_of_length top data.order
    (fun ts hlen => by
      rw [data.growth.params_eq_paramsOfOrder_append_of_length
        pref prefixTs hpref hprefixTs hlen]
      rw [List.reverse_append, mixedPartialList_append])
end BKAR.Forest.TerminalGrowth
