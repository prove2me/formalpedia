-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:40.270561+00:00
-- url     : https://prove2.me/submissions/a059b1d5-931e-4d90-89c1-ef07c52feaf3

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_CubePartition_Smoothness
import Theorems.Thm_BKAR_Forest_EdgeExtension_paramsOfOrder_append_singleton_continuous
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_standardInterp_intervalIntegrable


set_option autoImplicit false
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (h : Forest.EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        BKAR.mixedPartialList es ρ
          (F'.standardInterp
            (F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t]))))
      MeasureTheory.volume a b :=
  hρ.mixedPartialList_standardInterp_intervalIntegrable es F'
    (h.paramsOfOrder_append_singleton_continuous
      pref prefixTs hpref hprefixTs)
    a b
end BKAR.BKARContDiff
