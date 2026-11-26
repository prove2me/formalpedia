-- Prove2me | solution 1 for BKAR.Forest.mixedPartial_eq_mixedPartialList_of_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:03.448441+00:00
-- url     : https://prove2.me/submissions/6dc7af16-e2f1-4dc8-af23-182ccb50dc0d

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_PartialDerivSymmetry
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_eq_of_perm
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff


set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest
variable (F : Forest V)
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.Forest
theorem _root_.solution
    {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (hρ : BKARContDiff ρ) :
    F.mixedPartial ρ = BKAR.mixedPartialList order.reverse ρ := by
  have hperm : F.edges.toList.Perm order.reverse := by
    rw [List.perm_reverse]
    exact ((F.mem_edgeOrders_iff).mp horder).symm
  exact hρ.mixedPartialList_eq_of_perm hperm
end BKAR.Forest
