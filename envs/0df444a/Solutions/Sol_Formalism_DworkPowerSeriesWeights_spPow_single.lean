-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spPow_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:46.960891+00:00
-- url     : https://prove2.me/submissions/79faf4a7-aee3-4530-967b-dc2178f5dac6

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spCoeff_lin
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
theorem _root_.solution (s : σ) (i : ι) (a : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i a)
      ((∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ a) = N s i ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, MvPowerSeries.coeff_mul,
      Finset.sum_eq_single (Finsupp.single i a, Finsupp.single i 1)]
    · rw [ih, spCoeff_lin, pow_succ]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [if_neg, mul_zero]
        intro he
        exact hk ((Finsupp.single_left_inj one_ne_zero).mp he).symm
      · simp
    · rintro ⟨p1, p2⟩ hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h2 : MvPowerSeries.coeff p2 (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) = 0
      · rw [h2, mul_zero]
      · exfalso
        obtain ⟨k, -, hk2⟩ := spCoeff_lin_ne N s p2 h2
        subst hk2
        have hki : k = i := by
          by_contra hki
          have := DFunLike.congr_fun hp k
          simp [Ne.symm hki] at this
        subst hki
        apply hne
        have : p1 = Finsupp.single k a := by
          rw [show a + 1 = a + 1 from rfl, Finsupp.single_add] at hp
          exact add_right_cancel hp
        rw [this]
    · intro h
      exfalso; apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal, ← Finsupp.single_add]
end Formalism.DworkPowerSeriesWeights
