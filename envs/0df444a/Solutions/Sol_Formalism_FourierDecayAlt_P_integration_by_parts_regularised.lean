-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integration_by_parts_regularised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:57:15.709257+00:00
-- url     : https://prove2.me/submissions/258aa1f4-6c27-4967-b031-4fcbe41411aa

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_ibp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.RegIBP := B1.ibp
end Formalism.FourierDecayAlt.P
