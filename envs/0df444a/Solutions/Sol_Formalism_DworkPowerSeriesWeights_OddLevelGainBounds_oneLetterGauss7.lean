-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.oneLetterGauss7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:15.323161+00:00
-- url     : https://prove2.me/submissions/a034b023-f158-446e-9204-5c6c3b0e696f

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_GainDominatesOddLevelSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_one_letter_gauss_bound


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
theorem _root_.solution : OneLetterGauss7 := one_letter_gauss_bound
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
