-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.plus_letter_frame_of_data
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:44.279516+00:00
-- url     : https://prove2.me/submissions/9135ecb1-c651-47e1-aa09-9853fd3b58f4

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_plusStep_of

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
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.PlusAssemble := by
  unfold Formalism.FourierDecayAlt.Fr.PlusAssemble Formalism.FourierDecayAlt.Fr.PlusStep
  intro _ _ _ _ hLP hRTT hForm hTau hPL A S _ _ _ _ _ _ r L f a Ya h
  exact Formalism.FourierDecayAlt.P.Fr7.plusStep_of hLP hRTT hForm hTau hPL L f a Ya h
end Formalism.FourierDecayAlt.P
