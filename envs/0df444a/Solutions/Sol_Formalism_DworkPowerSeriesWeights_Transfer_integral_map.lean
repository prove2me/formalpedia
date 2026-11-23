-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.integral_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:40.683806+00:00
-- url     : https://prove2.me/submissions/d8422435-1b12-4249-8ca4-d59a8130ed5f

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
theorem _root_.solution (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {U : MvPowerSeries ι F}
    (h : Integral U) : Integral (map φ U) := by
  intro n
  rw [MvPowerSeries.coeff_map, hφ]
  exact h n
end Formalism.DworkPowerSeriesWeights.Transfer
