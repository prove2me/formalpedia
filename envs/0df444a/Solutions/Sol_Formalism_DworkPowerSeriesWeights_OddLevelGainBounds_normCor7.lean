-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.normCor7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:26:22.222433+00:00
-- url     : https://prove2.me/submissions/02e3ec0c-89e5-4bfd-a062-23087faab6a5

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_GainDominatesOddLevelSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_propSix7
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_gain_dominates_oddLevel_sum

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
theorem _root_.solution : NormCor7 := by
  intro l d _ hl hd he TT nu1 nu2 size k L w E pi y hpi0 hpi1 hk hw hE hD1 hD2 hy
  refine hy.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le ?_)
  have h6 := propSix7 l d hl hd he TT k (fun s => (Dl d TT nu1 size s : ℝ)) w E hk hw hE hD1 hD2
  have hsum : ∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum fun s _ => gain_dominates_oddLevel_sum l d (by omega) TT nu1 nu2 s
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [h6.1, h6.2]
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
