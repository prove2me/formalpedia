-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.qw_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:04.594877+00:00
-- url     : https://prove2.me/submissions/4f9f824b-a206-4755-b819-5fe0b2859869

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_frac
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_gt1

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
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 1 < |Y.re - l.pt.re|) : Pos (qw q0 w Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    obtain ⟨g1, g2⟩ := gt1 hl.2
    simp only [qw]
    split_ifs
    · apply pos_mul ih'
      have := frac (Y - l.pt) (by simp [hY, hl.1]) 1 0 (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
    · apply pos_mul ih'
      have := frac (l.pt - Y) (by simp [hY, hl.1]) 0 (-1) (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
end Formalism.FourierDecayAlt.P.Fr2
