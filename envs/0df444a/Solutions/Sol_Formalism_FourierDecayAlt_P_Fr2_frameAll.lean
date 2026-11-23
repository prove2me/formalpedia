-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.frameAll
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:25.549181+00:00
-- url     : https://prove2.me/submissions/7b72deef-2f50-4047-8992-9536a6880859

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_mem_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_ne

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
theorem _root_.solution (hS : StartFrame) (hM : StartModule) (hP : PlusStep) (hMi : MinusStep)
    (hF : FrameFree) (hW : WordJoint) : FrameAll := by
  intro A S _ _ _ _ _ _ r L st w hL hst hA
  induction w with
  | nil => exact hS hM A S r L st hst
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup := List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    have ihw := ih hAw
    have hfree := hF A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1
    obtain ⟨p0, p1, pm1, q0, qm1⟩ := hpt l (by simp)
    have hd := hpw'.1
    have hq := (hW A S r L st w).2.2.1
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
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      apply hP
      refine ⟨hL, ihw, hfree, hre l (by simp), m0, m1, ?_⟩
      rw [hq]
      exact qw_ne _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      apply hMi
      refine ⟨hL, ihw, hfree, hre l (by simp), m0, m1, mm1, ?_⟩
      rw [hq]
      exact qw_ne _ _ _ qm1 (fun l' hl' =>
        ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
end Formalism.FourierDecayAlt.P.Fr2
