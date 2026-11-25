-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.oneLetterGauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:25:22.350556+00:00
-- url     : https://prove2.me/submissions/b3f2501b-f634-4c98-9549-c196d5670e39

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_one_letter_gauss_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : OneLetterGauss := one_letter_gauss_sum
end Formalism.DworkPowerSeriesWeights
