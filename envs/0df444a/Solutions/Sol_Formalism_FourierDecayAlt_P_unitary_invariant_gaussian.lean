-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unitary_invariant_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:41.228945+00:00
-- url     : https://prove2.me/submissions/eeea8734-f259-47c3-931a-af350b197e0f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_unitaryInvariant

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.UnitaryInvariant := G8.unitaryInvariant
end Formalism.FourierDecayAlt.P
