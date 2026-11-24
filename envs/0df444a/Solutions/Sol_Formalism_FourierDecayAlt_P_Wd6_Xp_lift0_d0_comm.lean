-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.Xp_lift0_d0_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:24.216672+00:00
-- url     : https://prove2.me/submissions/511f37ee-5db1-4856-8941-283b97a666fa

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_entry_commute_R_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_rtt_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_diagScalar_commute_of_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_lift0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Xp_EC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_bT_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_hol_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_rel_plus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_vlet_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w) = d0 (bT σ w) * lift0 (Ts σ Y) * Xp w Y := by
  induction w with
  | nil => simp [Xp, bT, d0]
  | cons l w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    have ih := ih hw.2
    have c1 : d0 (vlet σ l) * Xp w Y = Xp w Y * d0 (vlet σ l) :=
      diagScalar_commute_of_entries (Xp_EC w Y (vlet_units σ l w hw.1))
    by_cases hl : l.plus
    · have c2 : d0 (bT σ w) * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) = Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * d0 (bT σ w) :=
        diagScalar_commute_of_entries (entry_commute_R_matrix (fun i j => (bT_free σ w hw.1 i j).symm) _)
      have s : Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * lift0 (Ts σ Y) * d0 (vlet σ l) =
          d0 (vlet σ l) * lift0 (Ts σ Y) * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) := by
        unfold vlet; rw [if_pos hl]
        exact rtt_relation _ _ _ _ (rel_plus hσ Y l.pt)
      simp only [Xp, bT, if_pos hl, diagScalar_mul]
      calc Xp w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * lift0 (Ts σ Y) * (d0 (vlet σ l) * d0 (bT σ w))
          = Xp w Y * (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * lift0 (Ts σ Y) * d0 (vlet σ l)) * d0 (bT σ w) := by
            simp only [mul_assoc]
        _ = (Xp w Y * d0 (vlet σ l)) * lift0 (Ts σ Y) * (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * d0 (bT σ w)) := by
            rw [s]; simp only [mul_assoc]
        _ = d0 (vlet σ l) * (Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w)) * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) := by
            rw [← c1, ← c2]; simp only [mul_assoc]
        _ = _ := by rw [ih]; simp only [mul_assoc]
    · have c3 : d0 (vlet σ l) * lift0 (Ts σ Y) = lift0 (Ts σ Y) * d0 (vlet σ l) := by
        refine diagScalar_commute_of_entries (EC_lift0 fun i j => ?_)
        unfold vlet; rw [if_neg hl]
        exact (ins_comm _ _ _ (io_free _ _) fun r s => io_comm (hol_star hσ Y l.pt i j r s)).symm
      simp only [Xp, bT, if_neg hl, diagScalar_mul]
      calc Xp w Y * lift0 (Ts σ Y) * (d0 (vlet σ l) * d0 (bT σ w))
          = Xp w Y * (lift0 (Ts σ Y) * d0 (vlet σ l)) * d0 (bT σ w) := by simp only [mul_assoc]
        _ = (Xp w Y * d0 (vlet σ l)) * lift0 (Ts σ Y) * d0 (bT σ w) := by
            rw [← c3]; simp only [mul_assoc]
        _ = d0 (vlet σ l) * (Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w)) := by
            rw [← c1]; simp only [mul_assoc]
        _ = _ := by rw [ih]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd6
