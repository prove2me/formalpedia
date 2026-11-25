-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covolume_assembly_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:46:54.24296+00:00
-- url     : https://prove2.me/submissions/6b8ccf9a-80f0-419f-8315-c4f2ab7ac4ad

import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Theorems.Thm_Formalism_ExtensionFiltration_covolume_assembly_weighted_holds


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
theorem _root_.solution : CovolumeEstimateAnchoredWeights := covolume_assembly_weighted_holds
end Formalism.ExtensionFiltration
