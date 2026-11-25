-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gaussian_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:41:20.617839+00:00
-- url     : https://prove2.me/submissions/b6f6d134-e05d-4fe2-9e39-00ca97ec961a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussOneDamped
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussOne_of_damped

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.GaussOne := G8.gaussOne_of_damped G8.gaussOneDamped
end Formalism.FourierDecayAlt.P
