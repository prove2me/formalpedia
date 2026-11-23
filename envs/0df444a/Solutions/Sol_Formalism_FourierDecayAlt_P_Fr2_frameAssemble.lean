-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.frameAssemble
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:06.341594+00:00
-- url     : https://prove2.me/submissions/2ea61d3d-218d-4afa-b110-d260f5233055

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_frameAll

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
theorem _root_.solution : FrameAssemble := by
  intro hS hM hP hMi hF hW
  have hA := frameAll hS hM hP hMi hF hW
  refine ⟨hA, ?_⟩
  intro A S _ _ _ _ _ _ r L st w hL hst hAd
  have h := hA A S r L st w hL hst hAd
  obtain ⟨w1, w2, w3, w4, w5⟩ := hW A S r L st w
  refine ⟨h.F_Fi, h.Fi_F, ?_, ?_, ?_⟩
  · have := h.form
    rw [w1] at this
    rw [this]; simp only [FrameData.d, w4]
  · intro Y hY
    have := h.frame_τ Y (by rw [w5]; exact hY)
    rw [w2] at this; exact this
  · intro Y hY hY1
    have := h.frame_l Y hY hY1
    rw [w2] at this; exact this
end Formalism.FourierDecayAlt.P.Fr2
