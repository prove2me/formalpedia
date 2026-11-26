-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:58.667469+00:00
-- url     : https://prove2.me/submissions/d28eb68c-e3ff-4ed5-aa21-ec3fa1b59077

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_integral_partialDeriv_interpWithFill_eq_extension
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
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution
    (h : EdgeExtension F F' e₀)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e) :
    (∫ t in a..b,
        partialDeriv e₀ (mixedPartialList es ρ) (F.interpWithFill u t)) =
      ∫ t in a..b, mixedPartialList (e₀ :: es) ρ
        (F'.interpWithFill (h.extendParam u t) t) := by
  simpa only [mixedPartialList_cons_apply] using
    h.integral_partialDeriv_interpWithFill_eq_extension u
      (mixedPartialList es ρ) a b hbound
end BKAR.Forest.EdgeExtension
