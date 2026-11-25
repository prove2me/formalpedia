-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cosetSumBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:30.382209+00:00
-- url     : https://prove2.me/submissions/5d42f883-8eac-4ec6-8e15-822938b3e204

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_corT_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.CorT := Formalism.FourierDecayAlt.P.BaseGramNonnegativity.corT_ok
end Formalism.FourierDecayAlt.P
