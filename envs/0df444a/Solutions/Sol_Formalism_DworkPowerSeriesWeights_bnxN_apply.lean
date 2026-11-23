-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnxN_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:22.590514+00:00
-- url     : https://prove2.me/submissions/79d75a37-b718-420c-affc-0e785b15deb3

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
theorem _root_.solution (m : V2 d →₀ ℕ) (s : ZMod d) : bnxN m s = m (false, s) + m (true, s) := by
  first
  | rfl
  | simp [bnxN]
end Formalism.DworkPowerSeriesWeights
