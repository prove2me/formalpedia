-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.map_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:45.777081+00:00
-- url     : https://prove2.me/submissions/8a5f3eb9-c707-4c83-ac8e-33ffb44e3f54

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer

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
open Formalism.IncomingBounds MvPowerSeries
open Formalism.DworkPowerSeriesWeights.Transfer
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
namespace Formalism.DworkPowerSeriesWeights.Transfer
theorem _root_.solution {ι : Type} {f : MvPowerSeries ι F} (h : constantCoeff f = 0) :
    map φ (mvExp f) = mvExp (map φ f) := by
  unfold mvExp
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h), PowerSeries.map_exp]
end Formalism.DworkPowerSeriesWeights.Transfer
