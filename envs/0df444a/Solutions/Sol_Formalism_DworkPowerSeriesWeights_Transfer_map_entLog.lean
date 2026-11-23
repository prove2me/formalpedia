-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.map_entLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:30.127684+00:00
-- url     : https://prove2.me/submissions/2e9831bc-dcb9-426c-92f6-b40a9dc645b9

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
theorem _root_.solution {N0 N1 : ℕ} (l : ℕ) (x : ZV d N0 N1) :
    map φ (entLog (K := F) l x) = entLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (entLog (K := F) l x n) = entLog (K := K) l x n
  simp only [entLog]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights.Transfer
