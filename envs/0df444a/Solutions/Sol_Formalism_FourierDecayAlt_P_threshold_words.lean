-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.threshold_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:46.4929+00:00
-- url     : https://prove2.me/submissions/a14361dd-85ed-4eb9-8aae-f797c6fa93fc

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_tWords_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_exponent_sizes
import Theorems.Thm_Formalism_FourierDecayAlt_P_massRatioFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_vandermondeWords


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.TWords := Sz5.tWords_of massRatioFormula exponent_sizes vandermondeWords
end Formalism.FourierDecayAlt.P
