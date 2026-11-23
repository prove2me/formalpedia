-- Prove2me | solution 1 for FRI_BadEvent_implies_MCA_BadEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:42:15.955808+00:00
-- url     : https://prove2.me/submissions/7cb4d3bb-306e-4143-bdb7-403f765546f2

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_folding_bad_implies_bad_event
import Theorems.Thm_FRI_BadEvent_eq_Folding_Bad_Event


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) (alpha : F) :
    FRI_BadEvent P f_0 bound i f_prev alpha →
    BadEvent (FRI_code P (i.succ)) (P.m i) (cast_folding_components P i f_prev)
      (FRI_distance_star P f_0 bound) (fun j ↦ alpha ^ (j : ℕ)) := by
  intro h
  have h_mca : BadEvent
      (reedSolomon (pow_domain (FRI_domain P i) (P.m i)) (FRI_degree P i / P.m i)) (P.m i)
      (folding_components (FRI_domain P i) (P.m i) (extend_by_zero (FRI_domain P i) f_prev))
      (FRI_distance_star P f_0 bound) (fun j ↦ alpha ^ (j : ℕ)) := by
    convert folding_bad_implies_bad_event ..
    · infer_instance
    · exact P.h_m_pos i
    · exact (FRI_BadEvent_eq_Folding_Bad_Event P f_0 bound i f_prev alpha).mp h
  convert h_mca using 1
  · congr! 1 with x
    simp [FRI_domain_succ_eq]
  · -- FRI_domain P (i.succ) = pow_domain (FRI_domain P i) (P.m i)
    have h_domain : FRI_domain P (i.succ) = pow_domain (FRI_domain P i) (P.m i) :=
      FRI_domain_succ_eq ..
    simp only [Fin.val_succ, FRI_code, FRI_degree, Fin.is_lt, ↓reduceDIte, Fin.eta]
    rw [← h_domain]
    rfl
  · unfold cast_folding_components folding_components
    simp only [Fin.val_succ] at *
    congr! 4 with x
    simp [FRI_domain_succ_eq]
