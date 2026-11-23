-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.evenIndicator_series_binomial_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:46.667962+00:00
-- url     : https://prove2.me/submissions/f6fe55e2-36fd-4818-93ef-23bc83294e5c

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
theorem _root_.solution : (s1 : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun _ => 1) (fun s => if s.val % 2 = 0 then 1 else 0) := by
  funext s
  simp only [s1, bnxA]
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
