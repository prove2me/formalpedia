-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spProd_ldeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:46.956993+00:00
-- url     : https://prove2.me/submissions/4f8aee8f-0a67-4b86-b6ac-d4bb7655428c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spPow_ldeg

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
variable {lt N} (hN : ∀ s k, N s k ≠ 0 → lt k = s)
include hN
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (S : Finset σ) (e : σ → ℕ) (n : ι →₀ ℕ)
    (h : MvPowerSeries.coeff n
      (∏ t ∈ S, (∑ k, MvPowerSeries.C (N t k) * MvPowerSeries.X k) ^ e t) ≠ 0) :
    ∀ t, spLdeg lt t n = if t ∈ S then e t else 0 := by
  induction S using Finset.induction_on generalizing n with
  | empty =>
    rw [Finset.prod_empty, MvPowerSeries.coeff_one] at h
    split_ifs at h with hn
    · intro t; subst hn; rw [spLdeg_zero]; simp
    · exact absurd rfl h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, MvPowerSeries.coeff_mul] at h
    obtain ⟨p, hp, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := left_ne_zero_of_mul hp'
    have h2 := right_ne_zero_of_mul hp'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    intro t
    rw [← hp, spLdeg_add, spPow_ldeg hN a (e a) p.1 h1 t, ih p.2 h2 t]
    by_cases hta : t = a
    · subst hta; simp [ha]
    · simp [hta]
end Formalism.DworkPowerSeriesWeights
