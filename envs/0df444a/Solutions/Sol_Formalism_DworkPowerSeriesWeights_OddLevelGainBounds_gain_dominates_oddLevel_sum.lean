-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gain_dominates_oddLevel_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:43.410549+00:00
-- url     : https://prove2.me/submissions/918cd941-29e3-4318-b8bc-1fc6e83a2321

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_GainDominatesOddLevelSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_gain_ge_inner_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution : GainDominatesInnerSum := gain_ge_inner_sum
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
