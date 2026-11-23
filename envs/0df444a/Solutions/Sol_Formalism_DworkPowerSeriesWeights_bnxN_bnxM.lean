-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnxN_bnxM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:28.503535+00:00
-- url     : https://prove2.me/submissions/69dc22e8-c85d-4736-a1ba-3ebdb1f0c1f9

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxN_apply
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxM_false
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxM_true

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
theorem _root_.solution (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) : bnxN (bnxM n k) = n := by
  ext s
  rw [bnxN_apply, bnxM_false, bnxM_true]
  have := hk s
  omega
end Formalism.DworkPowerSeriesWeights
