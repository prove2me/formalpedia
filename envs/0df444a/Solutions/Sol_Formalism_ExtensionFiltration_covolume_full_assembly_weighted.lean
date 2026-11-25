-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covolume_full_assembly_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:33.657716+00:00
-- url     : https://prove2.me/submissions/962e47c4-2984-4fba-8604-8df50d58f883

import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Theorems.Thm_Formalism_ExtensionFiltration_covolume_full_assembly_weighted_holds


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
theorem _root_.solution : CovolumeEstimateOfAverageDegreeWeighted := covolume_full_assembly_weighted_holds
end Formalism.ExtensionFiltration
