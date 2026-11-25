-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.theorem_A_matrix_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:39.479515+00:00
-- url     : https://prove2.me/submissions/e7c226a3-c61b-4b9d-9636-665766e4726b

import Definitions.Def_Formalism_GaussJetBounds_StatementV
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_thmAEntry_of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_thmAGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_thmAWeyl_of


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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmAEntry := thmAEntry_of (thmAWeyl_of thmAGauss)
end Formalism.DworkPowerSeriesWeights
