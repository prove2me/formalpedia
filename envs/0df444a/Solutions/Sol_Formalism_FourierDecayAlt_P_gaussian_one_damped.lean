-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gaussian_one_damped
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:41:13.951517+00:00
-- url     : https://prove2.me/submissions/99e25aba-b27f-4a83-99f6-88b17685ab9b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussOneDamped

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.GaussOneDamped := G8.gaussOneDamped
end Formalism.FourierDecayAlt.P
