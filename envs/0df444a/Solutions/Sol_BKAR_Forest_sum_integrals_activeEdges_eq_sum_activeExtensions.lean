-- Prove2me | solution 1 for BKAR.Forest.sum_integrals_activeEdges_eq_sum_activeExtensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:46.712551+00:00
-- url     : https://prove2.me/submissions/aada7dd8-4439-44f1-9bd8-4faaf765e35b

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in a..b,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by
  rw [← Finset.sum_attach F.activeEdges
    (fun e => ∫ t in a..b,
      mixedPartialList (e :: es) ρ (F.interpWithFill u t))]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [mixedPartialList_cons_apply] using
    ((extensions e).extension.integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
        es u ρ a b hbound)
end BKAR.Forest
