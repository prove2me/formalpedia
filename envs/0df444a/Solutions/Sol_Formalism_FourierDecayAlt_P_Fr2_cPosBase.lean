-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.cPosBase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:22.72957+00:00
-- url     : https://prove2.me/submissions/8cc673b4-cc53-4d29-80c5-bad50f93a0c2

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_div
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_xs_posB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_posB

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
theorem _root_.solution : CPosBase := by
  intro S _ _ x0 q0 w him hpw hpos e
  induction w with
  | nil => exact ⟨by simp [cs], by simp [cs]⟩
  | cons l w ih =>
    have hpw' := List.pairwise_cons.mp hpw
    have ih' := ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))
    obtain ⟨x1, x2, q1⟩ := hpos l (by simp)
    have hl := him l (by simp)
    have hy : (ypt l).im = 0 := by unfold ypt; split_ifs <;> simp [hl]
    have d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re - 1) ∧
        0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re + 1) := fun l' h =>
      ⟨him l' (by simp [h]), by
        rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> constructor <;> nlinarith⟩
    have d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧
        0 < ((ypt l + 1).re - (ypt l').re) * ((ypt l + 1).re - (ypt l').re - 1) := fun l' h =>
      ⟨him l' (by simp [h]), by
        simp only [Complex.add_re, Complex.one_re]
        rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> nlinarith⟩
    have X0 := xs_posB x0 w e _ hy x1 (fun l' h => ⟨(d0 l' h).1, (d0 l' h).2.1⟩)
    have X1 := xs_posB x0 w e _ (by simp [hy]) x2 d1
    have Q0 := qw_posB q0 w _ hy q1 d0
    simp only [cs]
    apply pos_mul ih'
    unfold ypt at X0 X1 Q0
    split_ifs at X0 X1 Q0 ⊢
    · exact pos_div Q0 X1
    · exact X0
    · exact pos_div Q0 X0
    · simpa using X1
end Formalism.FourierDecayAlt.P.Fr2
