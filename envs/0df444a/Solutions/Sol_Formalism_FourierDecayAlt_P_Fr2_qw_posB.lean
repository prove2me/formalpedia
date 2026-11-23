-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.qw_posB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:43.663946+00:00
-- url     : https://prove2.me/submissions/3cb1629e-15da-45eb-8bc6-8e7f6498e2f5

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_frac

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
variable {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (q0 : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (q0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1) ∧
      0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re + 1)) : Pos (qw q0 w Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    obtain ⟨hl, g1, g2⟩ := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [qw]
    unfold ypt at g1 g2
    split_ifs at g1 g2 ⊢
    · apply pos_mul ih'
      have := frac (Y - l.pt) (by simp [hY, hl]) 1 0 (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
    · apply pos_mul ih'
      have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at g1 g2 ⊢; nlinarith)
      simpa [sub_eq_add_neg] using this
end Formalism.FourierDecayAlt.P.Fr2
