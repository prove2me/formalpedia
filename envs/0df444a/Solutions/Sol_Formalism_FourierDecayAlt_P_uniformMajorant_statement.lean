-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.uniformMajorant_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:02:36.900855+00:00
-- url     : https://prove2.me/submissions/e6447cc5-8770-4fdc-aa4c-d3b3e492c8ef

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_UniformMajorant

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.UniformMajorant := Jx8.t_UniformMajorant
end Formalism.FourierDecayAlt.P
