-- Prove2me | solution 1 for Formalism.HC.Der.Rd.log_discr_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:27.551998+00:00
-- url     : https://prove2.me/submissions/e1c3bb37-5e51-47ec-a3c2-6a1ee408cf58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Theorems.Thm_Formalism_HC_Der_Rd_log_discr_tower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ
open Classical
namespace Formalism.HC.Der.Rd
theorem _root_.solution : Module.finrank E L * Real.log |(discr E : ℝ)| =
    ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
      Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
  have sum_log_aut_eq_sum_filter_lemma_4 {N : ℕ} [NeZero N] {L : Type _} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ N) (E : Type _) [Field E] [NumberField E] [Algebra E L] :
      ∑ τ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - τ ζ) : ℚ) : ℝ)| =
        ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
          (fun σ => ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
          Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
    refine Finset.sum_bij (fun τ _ => τ.restrictScalars ℚ) ?_ ?_ ?_ ?_
    · intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x; exact τ.commutes x
    · intro a _ b _ h; exact AlgEquiv.restrictScalars_injective ℚ h
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, Finset.mem_univ _, by ext x; rfl⟩
    · intro τ _; rfl
  have h1 := log_discr_tower hζ E
  have h2 := log_discr_tower hζ ℚ
  rw [NumberField.discr_rat] at h2
  simp only [Int.cast_one, abs_one, Real.log_one, mul_zero, add_zero] at h2
  have e1 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[E] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_erase _ (by simp [Algebra.norm_zero])
  have e2 : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[ℚ] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_erase _ (by simp [Algebra.norm_zero])
  have hsplit : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| +
      ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      ∑ σ : L ≃ₐ[ℚ] L, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsub := sum_log_aut_eq_sum_filter_lemma_4 hζ E
  linarith
end Formalism.HC.Der.Rd
