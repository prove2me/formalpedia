-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.minus_letter_last_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:22.368689+00:00
-- url     : https://prove2.me/submissions/e779b163-3437-464b-9bb1-8cbebd57e991

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_ee_conjugation

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
open Formalism.FourierDecayAlt.P.Fr3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.MinusLast := by
  intro A S _ _ _ _ _ _ r L f b Yb hH Y hY hY1
  obtain ⟨hL, hf, hfree, hre, i0, i1, im1, hq⟩ := hH
  have e := ee_conjugation A S r L f Y Yb hf hY.1 hY1.1 i0 i1 (by intro e; apply hY.2.1; rw [e]; ring)
  simp only [FrameData.minus]
  rw [e]
end Formalism.FourierDecayAlt.P
