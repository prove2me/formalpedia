-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phaseOk_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:27.21808+00:00
-- url     : https://prove2.me/submissions/c59664a4-04a1-48f9-baf0-637415677d9f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_PhaseOk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.PhaseOk := Jx8.t_PhaseOk
end Formalism.FourierDecayAlt.P
