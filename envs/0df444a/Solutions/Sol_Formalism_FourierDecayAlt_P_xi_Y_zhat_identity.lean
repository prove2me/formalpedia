-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.xi_Y_zhat_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:00:44.05911+00:00
-- url     : https://prove2.me/submissions/e2958970-6fb6-4ca6-9a02-05c5a7face5e

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CovecEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_XiYZhatIdentity
import Theorems.Thm_covector_entries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.C3.XiYZhat :=
  covector_entries
end Formalism.FourierDecayAlt.P
