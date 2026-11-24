-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.Lead_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:33.692571+00:00
-- url     : https://prove2.me/submissions/9e2d56ca-4de1-41ee-b85e-91aa98619cf9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_irrefl
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_add_right
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_add_left
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_add

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
theorem _root_.solution (hκ : Function.Injective κ) {f g : MvPolynomial σ R} {d d' : σ →₀ ℕ}
    (hf : Lead κ f d) (hg : Lead κ g d') : Lead κ (f * g) (d + d') := by
  classical
  have key : ∀ e e' : σ →₀ ℕ, e ∈ f.support → e' ∈ g.support → (e ≠ d ∨ e' ≠ d') →
      LL κ (e + e') (d + d') := by
    intro e e' he he' hne
    by_cases h1 : e = d
    · subst h1
      have h2 : e' ≠ d' := by
        rcases hne with h | h
        · exact absurd rfl h
        · exact h
      exact LL_add_left (hg.2 e' he' h2) e
    · by_cases h2 : e' = d'
      · subst h2
        exact LL_add_right (hf.2 e he h1) e'
      · exact LL_add hκ (hf.2 e he h1) (hg.2 e' he' h2)
  constructor
  · rw [MvPolynomial.coeff_mul, Finset.sum_eq_single (d, d')]
    · rw [hf.1, hg.1, one_mul]
    · rintro ⟨e, e'⟩ hmem hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
      simp only at hmem
      by_contra hc
      have he : e ∈ f.support := by
        rw [MvPolynomial.mem_support_iff]; intro h0; exact hc (by simp [h0])
      have he' : e' ∈ g.support := by
        rw [MvPolynomial.mem_support_iff]; intro h0; exact hc (by simp [h0])
      have hne' : e ≠ d ∨ e' ≠ d' := by
        by_contra hcc
        push Not at hcc
        exact hne (by rw [hcc.1, hcc.2])
      have := key e e' he he' hne'
      rw [hmem] at this
      exact LL_irrefl κ _ this
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (show (d, d').1 + (d, d').2 = d + d' from rfl)) h
  · intro e he hne
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g he)
    apply key a b ha hb
    by_contra hcc
    push Not at hcc
    exact hne (by rw [hcc.1, hcc.2])
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
