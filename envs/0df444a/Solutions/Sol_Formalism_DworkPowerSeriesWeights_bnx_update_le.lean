-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_update_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:37.125972+00:00
-- url     : https://prove2.me/submissions/dcee414b-2895-4580-8c5c-338c445c8fd3

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
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) :
    ∀ t, Function.update (⇑n) s j t ≤ n t := by
  intro t
  rw [Function.update_apply]
  split_ifs with h
  · subst h
    exact hj.le
  · exact le_rfl
end Formalism.DworkPowerSeriesWeights
