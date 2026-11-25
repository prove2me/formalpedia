-- Prove2me | solution 1 for Formalism.ExtensionFiltration.mean_height_sum_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:17.708814+00:00
-- url     : https://prove2.me/submissions/a3c0d501-9aff-422b-b819-7ef1a549308a

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_StatementF
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SumComponents
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Theorems.Thm_Formalism_ExtensionFiltration_combinedAverageDegreeBound_of
import Theorems.Thm_Formalism_ExtensionFiltration_meanHeightLowerBound
import Theorems.Thm_P2M_Formalism_ExtensionFiltration_sumComponents__a8bffc346fad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution : CombinedAverageDegreeBound := combinedAverageDegreeBound_of meanHeightLowerBound sumComponents'
end Formalism.ExtensionFiltration
