-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAEntryFull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:33.030851+00:00
-- url     : https://prove2.me/submissions/1d998dec-defb-47a3-8f81-f33a0e20c800

import Definitions.Def_Formalism_GaussJetBounds_StatementX
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_slope_bound_saturation
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_thmAEntry


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
theorem _root_.solution : ThmAEntryFull := by
  intro l _ d N0 N1 _ h3 h2 he K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size
    hn1 hn2 hsz a ha hsa hthr δ hδ
  exact thmAEntry l d N0 N1 h3 h2 he K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2
    size hn1 hn2 hsz a ha hsa hthr (slope_bound_saturation _ d N0 colN p hp) δ hδ
end Formalism.DworkPowerSeriesWeights
