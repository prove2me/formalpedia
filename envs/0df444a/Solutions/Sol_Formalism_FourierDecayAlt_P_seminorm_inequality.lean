-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.seminorm_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:07.220216+00:00
-- url     : https://prove2.me/submissions/54f58b99-e4b9-4ca4-95ca-58ef640b91b7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_semi

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
theorem _root_.solution : Formalism.FourierDecayAlt.B.SeminormIneq := B1.semi
end Formalism.FourierDecayAlt.P
