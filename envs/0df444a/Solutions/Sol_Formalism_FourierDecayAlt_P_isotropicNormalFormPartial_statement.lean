-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.isotropicNormalFormPartial_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:19:09.254834+00:00
-- url     : https://prove2.me/submissions/9d283691-c779-451d-a5b4-1a385ed70a76

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AAInvTrans
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsotropicNormalFormPartial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorsCommuteTranslations
import Theorems.Thm_isotropic_normal_form_partial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.C3.IsotropicNormalFormPartial := isotropic_normal_form_partial
end Formalism.FourierDecayAlt.P
