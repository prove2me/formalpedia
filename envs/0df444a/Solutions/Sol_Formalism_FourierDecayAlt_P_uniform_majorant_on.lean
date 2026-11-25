-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.uniform_majorant_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:55:00.914898+00:00
-- url     : https://prove2.me/submissions/37890ad4-ba88-4da6-a140-b2d47874b84b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_UniformMajorantOn

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.UniformMajorantOn := Jx8.t_UniformMajorantOn
end Formalism.FourierDecayAlt.P
