-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.outside_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:54:19.808567+00:00
-- url     : https://prove2.me/submissions/7c2952b9-15b4-40a7-a371-40521792475f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_OutsideOk

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.OutsideOk := Jx8.t_OutsideOk
end Formalism.FourierDecayAlt.P
