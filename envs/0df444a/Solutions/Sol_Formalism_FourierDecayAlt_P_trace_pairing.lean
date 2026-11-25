-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.trace_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:49:32.544093+00:00
-- url     : https://prove2.me/submissions/482da468-9659-456e-b935-0fb3a05e88e3

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_t_TracePairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.TracePairing := Jx3.t_TracePairing
end Formalism.FourierDecayAlt.P
