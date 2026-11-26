-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegral_eq_sum_integrals_mixedPartialList_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:42.477034+00:00
-- url     : https://prove2.me/submissions/49140069-4996-4b7a-9253-44d4133d782e

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp

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
    (es : List (Edge V))
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) :=
  singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp
    extensions hterm es 1 u ρ
end BKAR.Forest.ActiveTerminalBranchData
