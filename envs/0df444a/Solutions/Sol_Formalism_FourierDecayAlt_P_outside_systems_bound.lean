-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.outside_systems_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:44:30.477032+00:00
-- url     : https://prove2.me/submissions/23fbbf65-9c71-4388-80f5-14d9c2d4cc95

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_OutsideSysOk

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.OutsideSysOk := Jx8.t_OutsideSysOk
end Formalism.FourierDecayAlt.P
