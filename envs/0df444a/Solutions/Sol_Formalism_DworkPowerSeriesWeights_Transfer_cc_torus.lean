-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.cc_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:53.258222+00:00
-- url     : https://prove2.me/submissions/d59dd981-08f2-4816-be5f-5420a99ec513

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
theorem _root_.solution (l : ℕ) (ζ : F) (s : ZMod d) : constantCoeff (torus l ζ s) = 0 := by
  simp [torus]
end Formalism.DworkPowerSeriesWeights.Transfer
