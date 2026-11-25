-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.baseGramMonotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:39.947309+00:00
-- url     : https://prove2.me/submissions/8f4d7b73-38a0-4875-95a7-39f349673074

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGramMonotone__fdc49e4330af

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.BaseGramMonotone := Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGramMonotone'
end Formalism.FourierDecayAlt.P
