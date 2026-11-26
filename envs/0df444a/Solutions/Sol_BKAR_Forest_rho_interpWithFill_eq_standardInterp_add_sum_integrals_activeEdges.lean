-- Prove2me | solution 1 for BKAR.Forest.rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:36:08.707097+00:00
-- url     : https://prove2.me/submissions/4738eb74-1303-44d0-b144-760feeb090e1

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_sum_integrals_activeEdges_eq_sub
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_interpWithFill_zero
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
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    ρ (F.interpWithFill u b) =
      ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            partialDeriv e ρ (F.interpWithFill u t)) := by
  have hsum :
      Finset.sum F.activeEdges
        (fun e => ∫ t in 0..b,
          partialDeriv e ρ (F.interpWithFill u t)) =
        ρ (F.interpWithFill u b) - ρ (F.standardInterp u) := by
    simpa only [F.interpWithFill_zero u] using
      F.sum_integrals_activeEdges_eq_sub u ρ 0 b hρ hint
  calc
    ρ (F.interpWithFill u b) =
        (ρ (F.interpWithFill u b) - ρ (F.standardInterp u)) +
          ρ (F.standardInterp u) := by
          rw [sub_add_cancel]
    _ =
        ρ (F.standardInterp u) +
          (ρ (F.interpWithFill u b) - ρ (F.standardInterp u)) := by
          rw [add_comm]
    _ = ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            partialDeriv e ρ (F.interpWithFill u t)) := by
          rw [← hsum]
end BKAR.Forest
