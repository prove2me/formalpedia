-- Prove2me | solution 1 for BKAR.Forest.integral_activeEdgePartialSum_eq_sum_integrals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:07.136521+00:00
-- url     : https://prove2.me/submissions/fd50349a-2d9c-44cd-854c-54a9f4603960

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
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
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    (∫ t in a..b, F.activeEdgePartialSum u ρ t) =
      Finset.sum F.activeEdges
        (fun e => ∫ t in a..b,
          partialDeriv e ρ (F.interpWithFill u t)) := by
  simpa only [activeEdgePartialSum] using
    (intervalIntegral.integral_finsetSum
      (a := a) (b := b) (μ := MeasureTheory.volume)
      (s := F.activeEdges)
      (f := fun e t => partialDeriv e ρ (F.interpWithFill u t))
      hint)
end BKAR.Forest
