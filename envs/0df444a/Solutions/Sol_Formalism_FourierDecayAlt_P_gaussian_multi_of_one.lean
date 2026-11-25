-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gaussian_multi_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:50.9571+00:00
-- url     : https://prove2.me/submissions/e758170c-766b-4162-a508-8ba020ecf1f5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussMultiOfOne

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.GaussMultiOfOne := G8.gaussMultiOfOne
end Formalism.FourierDecayAlt.P
