-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.cPos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:22.609113+00:00
-- url     : https://prove2.me/submissions/65192ee8-f426-4011-a4d9-3d21c65faa85

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_div
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_xs_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_pos

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
theorem _root_.solution : CPos := by
  intro S _ _ x0 q0 w him hpw hpos e
  induction w with
  | nil => exact ⟨by simp [cs], by simp [cs]⟩
  | cons l w ih =>
    have hpw' := List.pairwise_cons.mp hpw
    have ih' := ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))
    obtain ⟨x1, x2, x3, q1, q2⟩ := hpos l (by simp)
    have hl := him l (by simp)
    have d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by have := hpw'.1 l' h; linarith⟩
    have d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt + 1).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by
        have := hpw'.1 l' h
        simp only [Complex.add_re, Complex.one_re]
        rcases lt_abs.mp this with g | g
        · exact lt_abs.mpr (Or.inl (by linarith))
        · exact lt_abs.mpr (Or.inr (by linarith))⟩
    have dm : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt - 1).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by
        have := hpw'.1 l' h
        simp only [Complex.sub_re, Complex.one_re]
        rcases lt_abs.mp this with g | g
        · exact lt_abs.mpr (Or.inl (by linarith))
        · exact lt_abs.mpr (Or.inr (by linarith))⟩
    simp only [cs]
    apply pos_mul ih'
    split_ifs
    · exact pos_div (qw_pos q0 w _ hl q1 d0) (xs_pos x0 w e _ (by simp [hl]) x2 d1)
    · exact xs_pos x0 w e _ hl x1 d0
    · exact pos_div (qw_pos q0 w _ (by simp [hl]) q2 dm) (xs_pos x0 w e _ (by simp [hl]) x3 dm)
    · exact xs_pos x0 w e _ hl x1 d0
end Formalism.FourierDecayAlt.P.Fr2
