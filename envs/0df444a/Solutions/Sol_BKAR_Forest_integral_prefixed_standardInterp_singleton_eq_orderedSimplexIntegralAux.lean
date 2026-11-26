-- Prove2me | solution 1 for BKAR.Forest.integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:05.08728+00:00
-- url     : https://prove2.me/submissions/ebca5097-2472-4b44-812c-247dc11afd14

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (G : Forest V) (e : Edge V)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..top,
        mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ [t])))) =
      orderedSimplexIntegralAux top [e]
        (fun ts => mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ ts)))) := by
  rfl
end BKAR.Forest
