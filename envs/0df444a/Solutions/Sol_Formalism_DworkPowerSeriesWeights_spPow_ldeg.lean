-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spPow_ldeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:17.43817+00:00
-- url     : https://prove2.me/submissions/7090c393-97bf-4405-8796-9b0572c9ceb4

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_single
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spCoeff_lin_ne

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
theorem _root_.solution (s : σ) (e : ℕ) (n : ι →₀ ℕ)
    (h : MvPowerSeries.coeff n ((∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ e) ≠ 0) :
    ∀ t, spLdeg lt t n = if t = s then e else 0 := by
  induction e generalizing n with
  | zero =>
    rw [pow_zero, MvPowerSeries.coeff_one] at h
    split_ifs at h with hn
    · intro t; subst hn; rw [spLdeg_zero]; split_ifs <;> rfl
    · exact absurd rfl h
  | succ e ih =>
    rw [pow_succ, MvPowerSeries.coeff_mul] at h
    obtain ⟨p, hp, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : MvPowerSeries.coeff p.1 ((∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ e) ≠ 0 :=
      left_ne_zero_of_mul hp'
    have h2 := right_ne_zero_of_mul hp'
    obtain ⟨k, hk, hk2⟩ := spCoeff_lin_ne N s p.2 h2
    have hks := hN s k hk
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    intro t
    rw [← hp, spLdeg_add, ih p.1 h1 t, hk2, spLdeg_single, hks]
    split_ifs with h3 h4 h4 <;> first | omega | (subst h3; exact absurd rfl h4) | exact absurd h4.symm h3
end Formalism.DworkPowerSeriesWeights
