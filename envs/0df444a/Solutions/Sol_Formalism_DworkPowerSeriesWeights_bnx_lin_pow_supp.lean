-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_lin_pow_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:01.51768+00:00
-- url     : https://prove2.me/submissions/0bfe2c10-2f76-4e2e-8ce4-afafc0a19a7e

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_lin_pow

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
theorem _root_.solution {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ)
    (a b : K) (k : ℕ) (μ : σ →₀ ℕ)
    (h : coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) ≠ 0) (z : σ) (hz : μ z ≠ 0) :
    z = x ∨ z = y := by
  rw [bnx_lin_pow] at h
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hr with hμ
  · subst hμ
    by_contra hne
    push_neg at hne
    apply hz
    simp [Finsupp.single_apply, Ne.symm hne.1, Ne.symm hne.2]
  · exact absurd rfl hr
end Formalism.DworkPowerSeriesWeights
