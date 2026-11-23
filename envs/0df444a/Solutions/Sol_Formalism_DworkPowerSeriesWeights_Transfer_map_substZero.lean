-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.map_substZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:57.57+00:00
-- url     : https://prove2.me/submissions/be7ace00-31fa-4145-bcf3-d871b52050ac

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
theorem _root_.solution (s : ZMod d) : map φ (s0 (K := F) s) = s0 s := by
  simp [s0]
end Formalism.DworkPowerSeriesWeights.Transfer
