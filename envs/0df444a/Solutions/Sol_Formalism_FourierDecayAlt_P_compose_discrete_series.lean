-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.compose_discrete_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:08.927212+00:00
-- url     : https://prove2.me/submissions/2c73afd7-c16e-4958-a58f-3b3f1fc3a196

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CutoffPlainAndSmoothed
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCost
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryU1Plain
import Theorems.Thm_differential_operator_compose


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.ComposeDD :=
  differential_operator_compose
end Formalism.FourierDecayAlt.P
