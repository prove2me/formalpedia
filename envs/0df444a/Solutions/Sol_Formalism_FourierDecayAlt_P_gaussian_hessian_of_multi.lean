-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gaussian_hessian_of_multi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:37.681794+00:00
-- url     : https://prove2.me/submissions/893404b5-2741-4c97-94fe-d06afc52af94

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussHessOfMulti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.GaussHessOfMulti := G8.gaussHessOfMulti
end Formalism.FourierDecayAlt.P
