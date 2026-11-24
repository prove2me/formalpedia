-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_module_of_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:54.304858+00:00
-- url     : https://prove2.me/submissions/9a277ac5-534a-4f18-b097-63d2b2e8dd5c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : WordJoint := by
  intro A S _ _ _ _ _ _ r L st w
  induction w with
  | nil =>
    refine ⟨rfl, ?_, ?_, rfl, ?_⟩
    · funext Y; rfl
    · funext Y; rfl
    · ext Y; simp [ofWord, Start.frame, Reg]
  | cons l w ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    by_cases hl : l.plus
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [ofWord, hl, FrameData.plus, RRw, h1, h2]
      · funext Y; simp [ofWord, hl, FrameData.plus, TTw, h2]
      · funext Y; simp [ofWord, hl, FrameData.plus, qw, h3]
      · simp [ofWord, hl, FrameData.plus, h4]
      · ext Y; simp [ofWord, hl, FrameData.plus, h5, Reg, RegL, and_comm]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [ofWord, hl, FrameData.minus, RRw, h1, h2]
      · funext Y; simp [ofWord, hl, FrameData.minus, TTw, h2]
      · funext Y; simp [ofWord, hl, FrameData.minus, qw, h3]
      · simp [ofWord, hl, FrameData.minus, h4]
      · ext Y; simp [ofWord, hl, FrameData.minus, h5, Reg, RegL, and_comm]
end Formalism.FourierDecayAlt.P
