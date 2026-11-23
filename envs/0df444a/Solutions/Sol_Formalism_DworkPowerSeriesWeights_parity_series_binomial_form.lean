-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.parity_series_binomial_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:45.474581+00:00
-- url     : https://prove2.me/submissions/e3cdd8cd-d7bd-498b-8987-e7ac41fb1ff7

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
theorem _root_.solution : (s2' : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun s => if s.val % 2 = 0 then 1 else 0) (fun s => if s.val % 2 = 0 then 0 else 1) := by
  funext s
  simp only [s2', bnxA]
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
