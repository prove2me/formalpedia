-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.paramsOfOrder_append_singleton_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:11.105106+00:00
-- url     : https://prove2.me/submissions/7531ee32-b202-4ccb-8131-53bf9e3f099b

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_CubePartition_Smoothness
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_continuous
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_eq_paramsOfOrder_append_singleton


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution
    (h : EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    Continuous
      (fun t : ℝ =>
        F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t])) := by
  have hfun :
      (fun t : ℝ =>
        F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t])) =
        fun t : ℝ => h.extendParam (F.paramsOfOrder pref prefixTs) t := by
    funext t
    rw [← h.extendParam_eq_paramsOfOrder_append_singleton
      pref prefixTs t hpref hprefixTs]
  rw [hfun]
  exact h.extendParam_continuous (F.paramsOfOrder pref prefixTs)
end BKAR.Forest.EdgeExtension
