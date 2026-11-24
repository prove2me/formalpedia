-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.propSix7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:06.663214+00:00
-- url     : https://prove2.me/submissions/d48a8bbc-b468-4cfc-b4ed-6341968fada9

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_GainDominatesOddLevelSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_proposition_six


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
theorem _root_.solution : PropSix7 := proposition_six
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
