-- Prove2me | solution 1 for BKAR.Forest.integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:39.588644+00:00
-- url     : https://prove2.me/submissions/0817997d-09d4-4920-9938-eb4eeddb4401

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_eq_paramsOfOrder_append_singleton
import Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_branchIntegralAux_eq_integral_tail_partialDeriv
import Theorems.Thm_BKAR_Forest_TerminalGrowth_ofActiveEdgesEqEmpty_branchIntegralAux
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_cons_apply



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : (choices F e).forest.activeEdges = ∅) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) =
      (TerminalGrowth.cons (choices F e)
          (TerminalGrowth.ofActiveEdgesEqEmpty
            (choices F e).forest hterm)).branchIntegralAux top
        (F.paramsOfOrder pref prefixTs) (mixedPartialList pref.reverse ρ) := by
  rw [TerminalGrowth.cons_branchIntegralAux_eq_integral_tail_partialDeriv]
  apply intervalIntegral.integral_congr
  intro t _
  change
    allBranchesBoundaryExpansion choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ =
      (TerminalGrowth.ofActiveEdgesEqEmpty
          (choices F e).forest hterm).branchIntegralAux t
        ((choices F e).extension.extendParam
          (F.paramsOfOrder pref prefixTs) t)
        (partialDeriv e.val (mixedPartialList pref.reverse ρ))
  rw [allBranchesBoundaryExpansion_activeEdges_card_of_activeEdges_eq_empty
    choices (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ
    hterm]
  rw [TerminalGrowth.ofActiveEdgesEqEmpty_branchIntegralAux]
  have horder : (pref ++ [e.val]).reverse = e.val :: pref.reverse := by
    rw [List.reverse_append]
    rfl
  have hparam :
      (choices F e).extension.extendParam
          (F.paramsOfOrder pref prefixTs) t =
        (choices F e).forest.paramsOfOrder (pref ++ [e.val])
          (prefixTs ++ [t]) :=
    (choices F e).extension.extendParam_eq_paramsOfOrder_append_singleton
      pref prefixTs t hpref hprefixTs
  rw [horder, ← hparam]
  rw [mixedPartialList_cons_apply]
end BKAR.Forest
