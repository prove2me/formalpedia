-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.q_radial_decomposition_of_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:52.631834+00:00
-- url     : https://prove2.me/submissions/6337182f-2b97-4fcd-8e6b-db47c42f911f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_RadialDecompositionOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QRadialDecompositionOfPieces
import Theorems.Thm_radial_decomposition_of_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts :=
  radial_decomposition_of_parts
end Formalism.FourierDecayAlt.P
