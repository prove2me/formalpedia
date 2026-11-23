-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:15.420637+00:00
-- url     : https://prove2.me/submissions/48753720-f17a-46a3-91e1-1da35a2a1bb5

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_ext_mulVec
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_vec_zero_of_form
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_adj_symm
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_form_adj
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_form_smul_left
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_form_smul_right
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_rankOne_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) (hH : Hc.PosDef)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ)
    (E : Matrix (Fin n) (Fin n) ℂ) (hEE : E * E = E)
    (hEc : ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ T ∈ 𝒯, M * T.map σ = T.map σ * M) → E * M = M * E)
    (χ : Matrix (Fin n) (Fin n) K → ℂ) :
    (∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = y) ∨ (∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = 0) := by
  by_cases hV : ∃ x0 ∈ simEig σ 𝒯 χ, x0 ≠ 0
  swap
  · push_neg at hV
    left
    intro y hy
    rw [hV y hy, Matrix.mulVec_zero]
  obtain ⟨x0, hx0, hx00⟩ := hV
  have hxe : ∀ x ∈ simEig σ 𝒯 χ, ∀ T ∈ 𝒯, (T.map σ) *ᵥ x = χ T • x := fun x hx => hx
  have hq : star x0 ⬝ᵥ Hc *ᵥ x0 ≠ 0 := fun h0 => hx00 (vec_zero_of_form hH x0 h0)
  have hconj : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ →
      starRingEnd ℂ (χ T') = χ T := by
    intro T hT T' hT' hTT
    have hf := form_adj hTT x0 x0
    rw [hxe x0 hx0 T hT, hxe x0 hx0 T' hT', form_smul_left, form_smul_right] at hf
    have h5 := mul_right_cancel₀ hq hf
    rw [← h5, starRingEnd_self_apply]
  have hcomm : ∀ y ∈ simEig σ 𝒯 χ, ∀ T ∈ 𝒯,
      rankOne Hc x0 y * T.map σ = T.map σ * rankOne Hc x0 y := by
    intro y hy T hT
    obtain ⟨T', hT', hTT⟩ := hadj T hT
    have hT'T := adj_symm hH hTT
    apply ext_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rankOne_mulVec, rankOne_mulVec,
      Matrix.mulVec_smul, hxe y hy T hT, ← form_adj hT'T, hxe x0 hx0 T' hT', form_smul_left,
      hconj T hT T' hT' hTT, smul_smul, mul_comm (χ T)]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c * (star x0 ⬝ᵥ Hc *ᵥ x0) = star x0 ⬝ᵥ Hc *ᵥ (E *ᵥ x0) :=
    ⟨_, div_mul_cancel₀ _ hq⟩
  have hEy : ∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = c • y := by
    intro y hy
    have h1 := congrArg (fun M => M *ᵥ x0) (hEc _ (hcomm y hy))
    simp only [← Matrix.mulVec_mulVec, rankOne_mulVec, Matrix.mulVec_smul] at h1
    apply smul_right_injective (Fin n → ℂ) hq
    show (star x0 ⬝ᵥ Hc *ᵥ x0) • (E *ᵥ y) = (star x0 ⬝ᵥ Hc *ᵥ x0) • (c • y)
    rw [h1, ← hcdef, smul_smul, mul_comm]
  have h2 : E *ᵥ (E *ᵥ x0) = E *ᵥ x0 := by rw [Matrix.mulVec_mulVec, hEE]
  rw [hEy x0 hx0, Matrix.mulVec_smul, hEy x0 hx0, smul_smul] at h2
  have h3 : (c * c - c) • x0 = 0 := by rw [sub_smul, h2, sub_self]
  have hcc : c * c - c = 0 := (smul_eq_zero.mp h3).resolve_right hx00
  have h4 : c * (c - 1) = 0 := by linear_combination hcc
  rcases mul_eq_zero.mp h4 with h0 | h0
  · right
    intro y hy
    rw [hEy y hy, h0, zero_smul]
  · left
    intro y hy
    rw [hEy y hy, sub_eq_zero.mp h0, one_smul]
end Formalism.DivisionValues.FinitelyNonzeroLinear
