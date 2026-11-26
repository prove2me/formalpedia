-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_branchIntegralAux_eq_integral_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:29.667383+00:00
-- url     : https://prove2.me/submissions/612c3bd3-5fd7-4af1-a2c0-9ade0e172d41

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
    (data : ActiveBranchData F) (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (data.growth e).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        (data.tail e).branchIntegralAux t
          ((data.extension e).extension.extendParam u t)
          (partialDeriv e.val ρ) :=
  (data.extension e).consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    (data.tail e) top u ρ
end BKAR.Forest.ActiveBranchData
