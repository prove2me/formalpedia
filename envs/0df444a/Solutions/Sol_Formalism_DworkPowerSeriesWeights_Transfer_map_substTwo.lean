-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.map_substTwo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:57.572811+00:00
-- url     : https://prove2.me/submissions/f6ea900d-21c1-4669-98b2-4cc2043cd6d9

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
theorem _root_.solution (s : ZMod d) : map φ (s2 (K := F) s) = s2 s := by
  unfold s2
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights.Transfer
