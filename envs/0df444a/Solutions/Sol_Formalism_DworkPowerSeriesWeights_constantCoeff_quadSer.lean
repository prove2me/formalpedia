-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.constantCoeff_quadSer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:06.046841+00:00
-- url     : https://prove2.me/submissions/cfc4f505-2b02-49e0-bb56-4aa2d4395aed

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer

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
theorem _root_.solution (c : ι → ι → K) :
    MvPowerSeries.constantCoeff (quadSer c) = 0 := by
  simp [quadSer]
end Formalism.DworkPowerSeriesWeights
