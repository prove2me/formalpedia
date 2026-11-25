-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integral_zero_frequency_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:09.992997+00:00
-- url     : https://prove2.me/submissions/6cd27b6b-ebf8-4081-8813-8c2b48a857ab

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_intZero

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
theorem _root_.solution : Formalism.FourierDecayAlt.B.IntRdZeroInv := B1.intZero
end Formalism.FourierDecayAlt.P
