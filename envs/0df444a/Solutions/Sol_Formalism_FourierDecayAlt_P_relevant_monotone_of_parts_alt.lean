-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.relevant_monotone_of_parts_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:52:44.952851+00:00
-- url     : https://prove2.me/submissions/e2ce572c-38ae-4bb3-92ba-159f54279459

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_relevant_monotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.RelevantMonoOfParts := fun _ _ _ _ => relevant_monotone
end Formalism.FourierDecayAlt.P
