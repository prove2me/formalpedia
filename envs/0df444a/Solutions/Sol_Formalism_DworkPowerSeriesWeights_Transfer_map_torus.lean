-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.map_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:57.579631+00:00
-- url     : https://prove2.me/submissions/982df0ca-2256-4f94-990f-a640a177bf03

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
variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}
namespace Formalism.DworkPowerSeriesWeights.Transfer
theorem _root_.solution (l : ℕ) (ζ : F) (s : ZMod d) :
    map φ (torus l ζ s) = torus l (φ ζ) s := by
  simp [torus]
end Formalism.DworkPowerSeriesWeights.Transfer
