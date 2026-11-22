-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnxM_false
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:00.841788+00:00
-- url     : https://prove2.me/submissions/d4bd171b-b8b5-4988-8e1c-144ab5668fd9

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
theorem _root_.solution (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) : bnxM n k (false, s) = k s := by
  first
  | rfl
  | simp [bnxM]
end Formalism.DworkPowerSeriesWeights
