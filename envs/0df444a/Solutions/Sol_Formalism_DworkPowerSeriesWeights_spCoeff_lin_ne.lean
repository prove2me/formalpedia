-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spCoeff_lin_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:53.128401+00:00
-- url     : https://prove2.me/submissions/feb49a10-2025-4fe4-a18c-4a16aba4cfe5

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spCoeff_lin

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
variable (lt : ι → σ) (N : σ → ι → R)
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (s : σ) (n : ι →₀ ℕ)
    (h : MvPowerSeries.coeff n (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ≠ 0) :
    ∃ k, N s k ≠ 0 ∧ n = Finsupp.single k 1 := by
  rw [spCoeff_lin] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases he : n = Finsupp.single k 1
  · rw [if_pos he, mul_one] at hk
    exact ⟨k, hk, he⟩
  · rw [if_neg he, mul_zero] at hk
    exact absurd rfl hk
end Formalism.DworkPowerSeriesWeights
