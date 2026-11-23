-- Prove2me | solution 1 for Csg.cbInnerGfp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:05.693804+00:00
-- url     : https://prove2.me/submissions/fc20fe1b-02ee-403d-a4d4-bb2841351af3

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbStageValue_t1
import Theorems.Thm_Csg_cbStageValue_t4
import Theorems.Thm_Csg_cbStageValue_t5
import Theorems.Thm_Csg_cbStageValue_t2
import Theorems.Thm_Csg_cbStageValue_t3
import Theorems.Thm_Csg_CSG_coBuchiInnerOpFun_coe
import Theorems.Thm_OrderHom_gfp_eq_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (b : CBState → Set.Icc (0 : ℝ) 1) :
    (cbCSG.coBuchiInnerOp cbU cbR_zero b).gfp = cbGClosed b := by
  refine OrderHom.gfp_eq_of_certificate _ _ ?_ ?_
  · funext s
    apply Subtype.ext
    change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b (cbGClosed b) s : ℝ) =
      cbGClosedVal (fun s' => (b s' : ℝ)) s
    rw [CSG.coBuchiInnerOpFun_coe]
    cases s with
    | t1 =>
      have hU : cbU .t1 := Or.inl rfl
      rw [if_pos hU, cbStageValue_t1]
      rfl
    | t2 =>
      have hU : cbU .t2 := Or.inr (Or.inl rfl)
      rw [if_pos hU, cbStageValue_t2]
      change min (cbGClosedVal (fun s' => (b s' : ℝ)) .t2)
          ((cbGClosedVal (fun s' => (b s' : ℝ)) .t1 +
            cbGClosedVal (fun s' => (b s' : ℝ)) .t3) / 2) =
        cbGClosedVal (fun s' => (b s' : ℝ)) .t2
      unfold cbGClosedVal
      rw [min_eq_left (le_refl _)]
    | t3 =>
      have hU : ¬ cbU .t3 := by unfold cbU; simp
      rw [if_neg hU, cbStageValue_t3]
      rfl
    | t4 =>
      have hU : cbU .t4 := Or.inr (Or.inr rfl)
      rw [if_pos hU, cbStageValue_t4]
      rfl
    | t5 =>
      have hU : ¬ cbU .t5 := by unfold cbU; simp
      rw [if_neg hU, cbStageValue_t5]
      rfl
  · intro w hw
    have hw3 : (w .t3 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t3 := by
      have hU : ¬ cbU .t3 := by unfold cbU; simp
      calc (w .t3 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t3 : ℝ) := hw .t3
        _ = cbCSG.stageValue .t3 (fun s' => (b s' : ℝ)) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t3 : ℝ) =
                cbCSG.stageValue .t3 (fun s' => (b s' : ℝ))
              rw [CSG.coBuchiInnerOpFun_coe, if_neg hU]
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t3 := by rw [cbStageValue_t3]; rfl
    have hw5 : (w .t5 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t5 := by
      have hU : ¬ cbU .t5 := by unfold cbU; simp
      calc (w .t5 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t5 : ℝ) := hw .t5
        _ = cbCSG.stageValue .t5 (fun s' => (b s' : ℝ)) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t5 : ℝ) =
                cbCSG.stageValue .t5 (fun s' => (b s' : ℝ))
              rw [CSG.coBuchiInnerOpFun_coe, if_neg hU]
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t5 := by rw [cbStageValue_t5]; rfl
    have hw4 : (w .t4 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t4 := by
      have hU : cbU .t4 := Or.inr (Or.inr rfl)
      calc (w .t4 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t4 : ℝ) := hw .t4
        _ = cbCSG.stageValue .t4 (fun s' => (w s' : ℝ)) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t4 : ℝ) =
                cbCSG.stageValue .t4 (fun s' => (w s' : ℝ))
              rw [CSG.coBuchiInnerOpFun_coe, if_pos hU]
        _ = (w .t5 : ℝ) := by rw [cbStageValue_t4]
        _ ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t5 := hw5
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t4 := rfl
    have hw1 : (w .t1 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t1 := by
      change (w .t1 : ℝ) ≤ 1
      exact (w .t1).2.2
    have hw2 : (w .t2 : ℝ) ≤ cbGClosedVal (fun s' => (b s' : ℝ)) .t2 := by
      have hU : cbU .t2 := Or.inr (Or.inl rfl)
      calc (w .t2 : ℝ) ≤ (cbCSG.coBuchiInnerOp cbU cbR_zero b w .t2 : ℝ) := hw .t2
        _ = min (w .t2 : ℝ) (((w .t1 : ℝ) + (w .t3 : ℝ)) / 2) := by
              change (cbCSG.coBuchiInnerOpFun cbU cbR_zero b w .t2 : ℝ) =
                min (w .t2 : ℝ) (((w .t1 : ℝ) + (w .t3 : ℝ)) / 2)
              rw [CSG.coBuchiInnerOpFun_coe, if_pos hU, cbStageValue_t2]
        _ ≤ ((w .t1 : ℝ) + (w .t3 : ℝ)) / 2 := min_le_right _ _
        _ ≤ (cbGClosedVal (fun s' => (b s' : ℝ)) .t1 +
              cbGClosedVal (fun s' => (b s' : ℝ)) .t3) / 2 := by
              gcongr
        _ = cbGClosedVal (fun s' => (b s' : ℝ)) .t2 := rfl
    intro s
    cases s with
    | t1 => exact hw1
    | t2 => exact hw2
    | t3 => exact hw3
    | t4 => exact hw4
    | t5 => exact hw5
end Csg
