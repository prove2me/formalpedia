-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAJet7_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:33.899614+00:00
-- url     : https://prove2.me/submissions/4c5b0173-b87e-42c6-af53-5107aa7ca5b1

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TheoremAMonomialOfLemmas
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_theorem_A_monomial_of_lemmas
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frame_pure_weight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaS
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemma_R_log_loss
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
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (hA : ThmAAssembly7) : ThmAJet7.{u} :=
  theorem_A_monomial_of_lemmas lemmaS.{u} lemma_R_log_loss.{u, 0} hA frame_pure_weight.{u}
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
