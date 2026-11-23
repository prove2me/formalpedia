-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:01.339157+00:00
-- url     : https://prove2.me/submissions/7fe5fcf7-d9bd-42e8-a64b-63fa21788cd9

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm

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
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi a b X v : ℝ} (h0 : 0 < pi) (hb : pi ^ v ≤ b) (ha : 0 ≤ a) (h : a * b ≤ X) :
    a ≤ X / pi ^ v := by
  have hp : 0 < pi ^ v := Real.rpow_pos_of_pos h0 v
  rw [le_div_iff₀ hp]
  exact (mul_le_mul_of_nonneg_left hb ha).trans h
end Formalism.DworkPowerSeriesWeights
