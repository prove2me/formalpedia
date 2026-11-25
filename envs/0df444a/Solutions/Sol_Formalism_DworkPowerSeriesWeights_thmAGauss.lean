-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAGauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:51.286041+00:00
-- url     : https://prove2.me/submissions/d8eba5a3-120c-4950-a7e5-9a3752ac116b

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAGaussOf
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_admissibleTransfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frame_jet_evaluation
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gauss_sum_powers
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_labelsExist_statement
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_thmAGauss_of


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
theorem _root_.solution : ThmAGauss :=
  thmAGauss_of admissibleTransfer frame_jet_evaluation labelsExist_statement gauss_sum_powers
end Formalism.DworkPowerSeriesWeights
