-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAJetA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:26.710368+00:00
-- url     : https://prove2.me/submissions/836aa589-1a4e-4da1-af39-514c738bc0d2

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_theorem_A_one_monomial_log_loss
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmAJetA.{u} := theorem_A_one_monomial_log_loss
end Formalism.DworkPowerSeriesWeights
