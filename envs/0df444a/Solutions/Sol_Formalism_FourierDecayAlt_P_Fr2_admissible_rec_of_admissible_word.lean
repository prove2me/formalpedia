-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.admissible_rec_of_admissible_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:03.723816+00:00
-- url     : https://prove2.me/submissions/cb4de7ac-b04f-49a1-ab6a-5892be6593c0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_mem_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_q_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution : AdmRecOfAdm := by
  intro A S _ _ _ _ _ _ r L st w hA
  induction w with
  | nil => trivial
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨p0, p1, pm1, q0, qm1⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : l.pt ∈ (ofWord L st w).inv := mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (ofWord L st w).inv := mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    refine ⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩
    by_cases hp : l.plus
    · simp only [hp, if_true]
      rw [q_eq]
      exact qw_ne _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    · simp only [hp]
      refine ⟨mm1, ?_⟩
      rw [q_eq]
      exact qw_ne _ _ _ qm1 (fun l' hl' =>
        ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
end Formalism.FourierDecayAlt.P.Fr2
