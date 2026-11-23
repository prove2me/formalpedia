-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.xs_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:06.605998+00:00
-- url     : https://prove2.me/submissions/c73dee68-ef91-4282-9009-d4dabd63332a

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_phi_pos

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
theorem _root_.solution (x0 : ℂ → ℂ) (w : List (Letter ℂ S)) (e : Ix S) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (x0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 1 < |Y.re - l.pt.re|) : Pos (xs x0 w e Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [xs]
    apply pos_mul ih'
    split_ifs
    · exact phi_pos l Y hY hl.1 hl.2
    · exact ⟨by simp, by simp⟩
end Formalism.FourierDecayAlt.P.Fr2
