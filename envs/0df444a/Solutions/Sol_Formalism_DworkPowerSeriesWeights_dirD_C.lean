-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dirD_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:57.582514+00:00
-- url     : https://prove2.me/submissions/2ff80a04-0484-4273-910e-4708b47508c4

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_apply

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
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (L : ι → K) (a : K) : dirD L (MvPowerSeries.C a : MvPowerSeries ι K) = 0 := by
  rw [dirD_apply]
  simp
end Formalism.DworkPowerSeriesWeights
