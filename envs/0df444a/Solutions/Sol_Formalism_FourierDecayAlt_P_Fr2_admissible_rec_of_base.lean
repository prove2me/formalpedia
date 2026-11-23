-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.admissible_rec_of_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:05.655298+00:00
-- url     : https://prove2.me/submissions/085f435f-68c2-4b70-a7f8-42eb4483f652

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_q_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_mem_invB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_neB

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
theorem _root_.solution : AdmRecOfBase := by
  intro A S _ _ _ _ _ _ r L st w hA
  induction w with
  | nil => trivial
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : AdmBase st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨p0, p1, p2, q0⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : ypt l ∈ (ofWord L st w).inv := mem_invB L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : ypt l + 1 ∈ (ofWord L st w).inv := mem_invB L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    have m2 : l.plus = false → ypt l + 2 ∈ (ofWord L st w).inv := fun hf => mem_invB L st w _ (p2 hf) (fun l' hl' =>
      ⟨fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have qq : (ofWord L st w).q (ypt l) ≠ 0 := by
      rw [q_eq]
      exact qw_neB _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    by_cases hp : l.plus
    · simp only [ypt, hp, if_true] at m0 m1 qq
      refine ⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩
      simp only [hp, if_true]; exact qq
    · have hf : l.plus = false := by simpa using hp
      have m2' := m2 hf
      simp only [ypt, hf, Bool.false_eq_true, if_false] at m0 m1 m2' qq
      refine ⟨ih hAw, hnd'.1, hre l (by simp), ?_, ?_, ?_⟩
      · have : l.pt - 1 + 1 = l.pt := by ring
        rwa [this] at m1
      · have : l.pt - 1 + 2 = l.pt + 1 := by ring
        rwa [this] at m2'
      · simp only [hf, Bool.false_eq_true, if_false]; exact ⟨m0, qq⟩
end Formalism.FourierDecayAlt.P.Fr2
