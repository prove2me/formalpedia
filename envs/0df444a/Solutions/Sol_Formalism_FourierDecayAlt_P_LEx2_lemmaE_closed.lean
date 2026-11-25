-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.lemmaE_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:18.943085+00:00
-- url     : https://prove2.me/submissions/c699fa7c-f466-4afb-976c-0a57db24a708

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_lemmaE
import Theorems.Thm_Formalism_FourierDecayAlt_P_cauchy_theta_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_markov_inequality_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : LemmaE :=
  lemmaE Formalism.FourierDecayAlt.P.cauchy_theta_identity Formalism.FourierDecayAlt.P.markov_inequality_vector
end Formalism.FourierDecayAlt.P.LEx2
