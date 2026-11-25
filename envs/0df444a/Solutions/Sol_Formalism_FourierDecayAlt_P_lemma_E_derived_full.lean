-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_E_derived_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:44:08.947288+00:00
-- url     : https://prove2.me/submissions/81a1595c-dde8-4a81-9544-5acc917b5205

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_lemmaEprimeFull_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.LemmaEprimeFull :=
  Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFull_closed
end Formalism.FourierDecayAlt.P
