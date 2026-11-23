-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spPair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:38.466539+00:00
-- url     : https://prove2.me/submissions/ab7b84f4-ba08-4eb6-a415-7694318e3b38

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_eq_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spPow_ldeg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spPow_single

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
theorem _root_.solution (i j : ι) (a b : ℕ) (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
      ((∑ k, MvPowerSeries.C (N (lt i) k) * MvPowerSeries.X k) ^ a *
        (∑ k, MvPowerSeries.C (N (lt j) k) * MvPowerSeries.X k) ^ b) =
      N (lt i) i ^ a * N (lt j) j ^ b := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single i a, Finsupp.single j b)]
  · rw [spPow_single hN, spPow_single hN]
  · rintro ⟨p1, p2⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : MvPowerSeries.coeff p1
        ((∑ k, MvPowerSeries.C (N (lt i) k) * MvPowerSeries.X k) ^ a) = 0
    · rw [h1, zero_mul]
    by_cases h2 : MvPowerSeries.coeff p2
        ((∑ k, MvPowerSeries.C (N (lt j) k) * MvPowerSeries.X k) ^ b) = 0
    · rw [h2, mul_zero]
    exfalso
    have l1 := spPow_ldeg hN (lt i) a p1 h1
    have l2 := spPow_ldeg hN (lt j) b p2 h2
    have z1 : ∀ k, lt k ≠ lt i → p1 k = 0 := fun k hk =>
      spLdeg_eq_zero lt p1 k (by rw [l1, if_neg hk])
    have z2 : ∀ k, lt k ≠ lt j → p2 k = 0 := fun k hk =>
      spLdeg_eq_zero lt p2 k (by rw [l2, if_neg hk])
    have e1 : p1 = Finsupp.single i a := by
      ext k
      have hk := DFunLike.congr_fun hp k
      simp only [Finsupp.add_apply] at hk
      by_cases hki : lt k = lt i
      · have hkj : lt k ≠ lt j := hki ▸ hij
        have hkj' : j ≠ k := fun h => hkj (h ▸ rfl)
        rw [z2 k hkj, add_zero] at hk
        rw [hk]; simp [Finsupp.single_apply, hkj']
      · have hki' : i ≠ k := fun h => hki (h ▸ rfl)
        rw [z1 k hki, Finsupp.single_apply, if_neg hki']
    have e2 : p2 = Finsupp.single j b := by
      rw [e1] at hp; exact add_left_cancel hp
    exact hne (by rw [e1, e2])
  · intro h; exfalso; apply h; rw [Finset.HasAntidiagonal.mem_antidiagonal]
end Formalism.DworkPowerSeriesWeights
