-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:21:24.225812+00:00
-- url     : https://prove2.me/submissions/6664971d-0203-4f39-83e4-a3ee0bdff9f8

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution
    (data : ActiveBranchData F)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (data.terminal e).activeEdges = ∅)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (b : ℝ) :
    (data.growth e).branchIntegrand u ρ ts =
      mixedPartialList (e.val :: data.order e).reverse ρ
        ((data.terminal e).interpWithFill
          ((data.growth e).params u ts) b) :=
  (data.growth e).branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    u ρ ts b (hterm e)
end BKAR.Forest.ActiveBranchData
