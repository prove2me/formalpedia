-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_degree_bnxM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:48.583502+00:00
-- url     : https://prove2.me/submissions/d7524b9d-e2d4-4e8a-ad4a-cc92f78a41e6

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
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
theorem _root_.solution (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) :
    (bnxM n k).degree = n.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, bnxM_true, bnxM_false]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by have := hk s; omega
end Formalism.DworkPowerSeriesWeights
