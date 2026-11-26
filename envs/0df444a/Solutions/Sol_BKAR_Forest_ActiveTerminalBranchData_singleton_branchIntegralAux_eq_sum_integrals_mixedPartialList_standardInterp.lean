-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:25:20.92234+00:00
-- url     : https://prove2.me/submissions/97b48d66-ff05-4207-bb37-cc9526ff7dbd

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegralAux top u
        (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) :=
  ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
    extensions es top u ρ hterm
end BKAR.Forest.ActiveTerminalBranchData
