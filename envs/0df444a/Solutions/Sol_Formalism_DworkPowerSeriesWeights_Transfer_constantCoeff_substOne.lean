-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:06.971809+00:00
-- url     : https://prove2.me/submissions/6337a968-41c2-4a29-9435-90069484c5d2

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
theorem _root_.solution (s : ZMod d) : constantCoeff (s1 (K := F) s) = 0 := by
  unfold s1
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights.Transfer
