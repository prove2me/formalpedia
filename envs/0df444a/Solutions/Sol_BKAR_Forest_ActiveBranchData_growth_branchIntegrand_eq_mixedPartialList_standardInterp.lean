-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_branchIntegrand_eq_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:21:30.038371+00:00
-- url     : https://prove2.me/submissions/9f7c2341-6a92-4f6c-9c88-6f8f45c0b721

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def_standardInterp


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
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) :
    (data.growth e).branchIntegrand u ρ ts =
      mixedPartialList (e.val :: data.order e).reverse ρ
        ((data.terminal e).standardInterp ((data.growth e).params u ts)) :=
  (data.growth e).branchIntegrand_def_standardInterp u ρ ts
end BKAR.Forest.ActiveBranchData
