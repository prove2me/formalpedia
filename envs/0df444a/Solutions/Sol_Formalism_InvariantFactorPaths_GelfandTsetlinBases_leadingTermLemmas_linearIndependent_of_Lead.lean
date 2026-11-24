-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.linearIndependent_of_Lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:27.924628+00:00
-- url     : https://prove2.me/submissions/2a8035b4-0037-4cf1-b138-d1c751aeeb52

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_irrefl
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_exists_LL_max

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {σ τ : Type*} [LinearOrder τ] (κ : σ → τ)
variable {κ}
variable {R : Type*} [CommRing R] (κ)
variable {κ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (hκ : Function.Injective κ) {k : Type*} [Field k] {ι : Type*}
    (v : ι → MvPolynomial σ k) (d : ι → σ →₀ ℕ) (hd : Function.Injective d)
    (hv : ∀ i, Lead κ (v i) (d i)) : LinearIndependent k v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁, hg₁⟩ := hcon
  have hne : (s.filter fun i => g i ≠ 0).Nonempty := ⟨i₁, Finset.mem_filter.2 ⟨hi₁, hg₁⟩⟩
  obtain ⟨i₀, hi₀, hmax⟩ := exists_LL_max hκ d hd _ hne
  have hc : coeff (d i₀) (∑ i ∈ s, g i • v i) = 0 := by rw [hsum]; simp
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single i₀] at hc
  · rw [MvPolynomial.coeff_smul, (hv i₀).1, smul_eq_mul, mul_one] at hc
    exact (Finset.mem_filter.1 hi₀).2 hc
  · intro j hj hji
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have h1 := hmax j (Finset.mem_filter.2 ⟨hj, hgj⟩) hji
      by_contra hc'
      have hsup : d i₀ ∈ (v j).support := by
        rw [MvPolynomial.mem_support_iff]; intro h0; exact hc' (by rw [h0, mul_zero])
      have h2 := (hv j).2 (d i₀) hsup (fun h => hji (hd h).symm)
      exact LL_irrefl κ _ (LL_trans hκ h1 h2)
  · intro h
    exact absurd (Finset.mem_filter.1 hi₀).1 h
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
