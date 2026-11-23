-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.frameRecAssemble
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:25.396154+00:00
-- url     : https://prove2.me/submissions/3415d844-b0fb-4dfe-9ce8-9fc4c41a7eeb

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord

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
theorem _root_.solution : FrameRecAssemble := by
  intro h0 hm hp hn hf A S _ _ _ _ _ _ r L st w hL hs
  induction w with
  | nil => intro _; exact h0 hm A S r L st hs
  | cons l w ih =>
    rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hw := ih h1
    have hfr := hf A S r L st w l.intersection_update_fsHerm_neg_one h2
    by_cases hl : l.plus
    · simp only [hl, if_true] at h6
      simp only [ofWord, hl, if_true]
      exact hp A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6⟩
    · simp only [hl] at h6
      simp only [ofWord, hl]
      exact hn A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6.1, h6.2⟩
end Formalism.FourierDecayAlt.P.Fr2
