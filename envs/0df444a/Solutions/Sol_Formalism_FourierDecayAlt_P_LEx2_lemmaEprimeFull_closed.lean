-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFull_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:08.491811+00:00
-- url     : https://prove2.me/submissions/24b48f59-752d-419c-9914-1b5d27828f60

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_lemmaEprimeFull_fromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_derived_energy_L2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_epCoefInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_lemmaEprime


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
theorem _root_.solution : LemmaEprimeFull :=
  lemmaEprimeFull_fromSteps derived_energy_L2 epCoefInt lemmaEprime
end Formalism.FourierDecayAlt.P.LEx2
