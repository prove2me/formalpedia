-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmOne_lin_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:14.407146+00:00
-- url     : https://prove2.me/submissions/a5289510-c9ee-400f-97a6-f183aab7f1b3

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] {ι : Type v} [Fintype ι] (c : ι → K) :
    MvPowerSeries.constantCoeff (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) = 0 := by
  simp [map_sum]
end Formalism.DworkPowerSeriesWeights
