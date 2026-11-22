-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnxM_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:47.385436+00:00
-- url     : https://prove2.me/submissions/5e39d8f6-aa2b-463b-a6ca-32c348778a6a

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
theorem _root_.solution (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) :
    bnxM n k (true, s) = n s - k s := by
  first
  | rfl
  | simp [bnxM]
end Formalism.DworkPowerSeriesWeights
