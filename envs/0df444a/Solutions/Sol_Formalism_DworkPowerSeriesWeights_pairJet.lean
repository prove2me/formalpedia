-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pairJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:15.998565+00:00
-- url     : https://prove2.me/submissions/ff474cdb-5fce-42da-8445-6d9121bea0f4

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_pair_jet_bound
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : PairJet.{u} := pair_jet_bound
end Formalism.DworkPowerSeriesWeights
