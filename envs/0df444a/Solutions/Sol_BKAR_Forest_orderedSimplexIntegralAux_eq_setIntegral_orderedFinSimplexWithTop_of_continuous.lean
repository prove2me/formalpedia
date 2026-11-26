-- Prove2me | solution 1 for BKAR.Forest.orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:13.683854+00:00
-- url     : https://prove2.me/submissions/76b4bd31-da96-436d-a931-831f72b838c8

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_integrableOn_orderedFinSimplexWithTop_of_continuous
import Theorems.Thm_BKAR_Forest_setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
import Theorems.Thm_BKAR_Forest_finCons_getD_cons_of_length
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_ListPathContinuous_comp
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr_of_length
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    {top : ℝ} (htop : 0 ≤ top) :
    ∀ (order : List (Edge V)) (G : (Fin order.length → ℝ) → ℝ),
      Continuous G →
        orderedSimplexIntegralAux top order
          (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
        ∫ xs in orderedFinSimplexWithTop top order.length, G xs
  | [], G, _hG => by
      rw [orderedSimplexIntegralAux_nil]
      change
        G (fun i : Fin 0 => ([] : List ℝ).getD i.val 0) =
          ∫ xs in orderedFinSimplexWithTop top 0, G xs
      have hleft :
          (fun i : Fin 0 => ([] : List ℝ).getD i.val 0) =
            (default : Fin 0 → ℝ) :=
        Subsingleton.elim _ _
      rw [hleft]
      have hset : orderedFinSimplexWithTop top 0 = Set.univ := by
        ext xs
        simp [orderedFinSimplexWithTop]
      rw [hset, setIntegral_univ]
      change G (fun _ : Fin 0 => (default : ℝ)) =
        ∫ x, G x ∂(volume : Measure (Fin 0 → ℝ))
      have huniq :=
        MeasureTheory.integral_unique
          (μ := (volume : Measure (Fin 0 → ℝ)))
          (fun y : Fin 0 → ℝ => G y)
      have huniqEq := by
        simpa [Measure.real, volume_pi, Measure.pi_of_empty] using huniq.symm
      exact (congrArg G (Subsingleton.elim (fun _ : Fin 0 => (default : ℝ)) _)).trans
        huniqEq
  | e :: order, G, hG => by
      have hfull :
          IntegrableOn G (orderedFinSimplexWithTop top (order.length + 1)) :=
        integrableOn_orderedFinSimplexWithTop_of_continuous hG
      have hset :
          ∫ xs in orderedFinSimplexWithTop top (order.length + 1), G xs =
            ∫ t in 0..top,
              ∫ us in orderedFinSimplexWithTop t order.length, G (Fin.cons t us) :=
        setIntegral_orderedFinSimplexWithTop_succ_eq_iterated_interval
          htop order.length G hfull
      rw [orderedSimplexIntegralAux_cons]
      calc
        ∫ t in 0..top,
            orderedSimplexIntegralAux t order
              (fun ts =>
                G (fun i : Fin (e :: order).length => (t :: ts).getD i.val 0))
            =
          ∫ t in 0..top,
            ∫ us in orderedFinSimplexWithTop t order.length, G (Fin.cons t us) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc (0 : ℝ) top := by
              simpa [Set.uIcc_of_le htop] using ht
            let Gt : (Fin order.length → ℝ) → ℝ :=
              fun us => G (Fin.cons t us)
            have hGt : Continuous Gt := by
              exact hG.comp
                ((continuous_const : Continuous fun _ : Fin order.length → ℝ => t).finCons
                  continuous_id)
            calc
              orderedSimplexIntegralAux t order
                  (fun ts =>
                    G (fun i : Fin (e :: order).length => (t :: ts).getD i.val 0))
                  =
                orderedSimplexIntegralAux t order
                  (fun ts => Gt (fun i : Fin order.length => ts.getD i.val 0)) := by
                  apply orderedSimplexIntegralAux_congr_of_length
                  intro ts hlen
                  dsimp [Gt]
                  congr 1
                  simpa using finCons_getD_cons_of_length t ts hlen
              _ = ∫ us in orderedFinSimplexWithTop t order.length, Gt us := by
                  exact
                    solution
                      htIcc.1 order Gt hGt
              _ = ∫ us in orderedFinSimplexWithTop t order.length, G (Fin.cons t us) := rfl
        _ = ∫ xs in orderedFinSimplexWithTop top (order.length + 1), G xs := hset.symm
end BKAR.Forest
