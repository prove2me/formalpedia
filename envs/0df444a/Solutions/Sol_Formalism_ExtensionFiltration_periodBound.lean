-- Prove2me | solution 1 for Formalism.ExtensionFiltration.periodBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:52.475995+00:00
-- url     : https://prove2.me/submissions/1d1f5893-6a3e-4754-bd5f-2bf4db13096a

import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Theorems.Thm_P2M_Formalism_ExtensionFiltration_period_bound__2065990858fe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution : PeriodBound := period_bound'
end Formalism.ExtensionFiltration
