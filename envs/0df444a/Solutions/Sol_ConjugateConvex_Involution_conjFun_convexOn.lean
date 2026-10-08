-- Prove2me | solution 1 for ConjugateConvex.Involution.conjFun_convexOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:02:21.789982+00:00
-- url     : https://prove2.me/submissions/2139b82a-237f-4c62-a476-c800e8309f44

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

set_option autoImplicit false

open ConjugateConvex.Involution in
theorem afbb8d07_key {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    {ξ₁ ξ₂ : Fin n → ℝ} (h₁ : ξ₁ ∈ conjDomain G f) (h₂ : ξ₂ ∈ conjDomain G f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∀ y ∈ (fun x => x ⬝ᵥ (a • ξ₁ + b • ξ₂) - f x) '' G,
      y ≤ a * conjFun G f ξ₁ + b * conjFun G f ξ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  have e1 : x ⬝ᵥ ξ₁ - f x ≤ conjFun G f ξ₁ := le_csSup h₁ ⟨x, hx, rfl⟩
  have e2 : x ⬝ᵥ ξ₂ - f x ≤ conjFun G f ξ₂ := le_csSup h₂ ⟨x, hx, rfl⟩
  have hexp : x ⬝ᵥ (a • ξ₁ + b • ξ₂) - f x
      = a * (x ⬝ᵥ ξ₁ - f x) + b * (x ⬝ᵥ ξ₂ - f x) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    linear_combination (f x) * hab
  change x ⬝ᵥ (a • ξ₁ + b • ξ₂) - f x ≤ _
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

open ConjugateConvex.Involution in
theorem solution {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    ConvexOn ℝ (conjDomain G f) (conjFun G f) := by
  refine ⟨?_, ?_⟩
  · intro ξ₁ h₁ ξ₂ h₂ a b ha hb hab
    exact ⟨_, afbb8d07_key G f h₁ h₂ ha hb hab⟩
  · intro ξ₁ h₁ ξ₂ h₂ a b ha hb hab
    rcases G.eq_empty_or_nonempty with hG | hG
    · simp [conjFun, hG]
    · show sSup _ ≤ _
      refine csSup_le (hG.image _) (afbb8d07_key G f h₁ h₂ ha hb hab)
