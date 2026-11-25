-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:24.811112+00:00
-- url     : https://prove2.me/submissions/123be448-0e68-4370-ac78-581131e44420

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_theorem_A_matrix_entries


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
theorem _root_.solution : ThmAEntry := theorem_A_matrix_entries
end Formalism.DworkPowerSeriesWeights
