-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.theorem_A_one_monomial_log_loss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:01.323548+00:00
-- url     : https://prove2.me/submissions/28c7cb48-c0cd-499c-9db2-6388cd2992bb

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ThmAJetA_of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frame_pure_weight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaS
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemma_R_log_loss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowRadiusAssembly
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmAJetA.{u} :=
  ThmAJetA_of lemmaS.{u} lemma_R_log_loss.{u, 0} rowRadiusAssembly frame_pure_weight.{u}
end Formalism.DworkPowerSeriesWeights
