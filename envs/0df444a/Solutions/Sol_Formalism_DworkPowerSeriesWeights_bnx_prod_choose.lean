-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_prod_choose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:31.762274+00:00
-- url     : https://prove2.me/submissions/6f0e7b21-9326-4a47-9808-4b82a92af6c7

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
theorem _root_.solution (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) (e : ZMod d → K)
    (he : e s = 1) :
    ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * e t ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = ((n s).choose j : K) := by
  rw [Finset.prod_eq_single s]
  · first
    | (rw [Function.update_apply, if_pos rfl, he, one_pow, one_pow, one_mul, one_mul,
        Nat.add_sub_cancel' hj.le])
    | simp [Function.update_apply, he, Nat.add_sub_cancel' hj.le]
  · intro t _ hts
    simp [Function.update_apply, hts]
  · intro h
    exact absurd (Finset.mem_univ s) h
end Formalism.DworkPowerSeriesWeights
