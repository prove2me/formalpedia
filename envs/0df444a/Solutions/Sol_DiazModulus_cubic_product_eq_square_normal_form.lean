-- Prove2me | solution 1 for DiazModulus.cubic_product_eq_square_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-05T08:40:17.785984+00:00
-- url     : https://prove2.me/submissions/c53a0870-71c4-42fe-a3be-302236471c94

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# A square that is a product of two cubics: the normal form `G · (Q₀ Q₁, Q₁², Q₀²)`

Let `P₀, P₁` be independent polynomials over a field `K` with `P₁ P₂ = P₀²` and
`deg P₁, deg P₂ ≤ 3`. Then there are independent `Q₀, Q₁` of degree at most one and a combination
`G = a Q₀ + b Q₁` with `P₀ = G Q₀ Q₁`, `P₁ = G Q₁²` and `P₂ = G Q₀²`.

**Proof.**
1. Divide out the common factor: `P₀ = d Q₀`, `P₁ = d Q₁` with `Q₀, Q₁` coprime.
2. `Q₁ P₂ = d Q₀²` and `Q₁` is coprime to `Q₀²`, so `d = Q₁ G`; hence `P₀ = G Q₀ Q₁`, `P₁ = G Q₁²`
   and `P₂ = G Q₀²`. Degrees add, so `deg G + 2 deg Qᵢ ≤ 3` and `deg Qᵢ ≤ 1`.
3. `s Q₀ + t Q₁ = 0` gives `s P₀ + t P₁ = 0`, so `Q₀, Q₁` are independent. Two independent
   polynomials of degree at most one are not both constant, so `deg G ≤ 1`, and they span every
   polynomial of degree at most one (Cramer's rule on the coefficients); in particular `G`.
-/

namespace R4B_cubic

open Polynomial

variable {K : Type*} [Field K]

/-- Two independent polynomials of degree at most one: one of them has degree one, and every
polynomial of degree at most one is a combination of them. -/
theorem linear_pair {Q₀ Q₁ : K[X]} (h₀ : Q₀.natDegree ≤ 1) (h₁ : Q₁.natDegree ≤ 1)
    (hli : LinearIndependent K ![Q₀, Q₁]) :
    (Q₀.natDegree = 1 ∨ Q₁.natDegree = 1) ∧
      ∀ g : K[X], g.natDegree ≤ 1 → ∃ a b : K, g = C a * Q₀ + C b * Q₁ := by
  rw [LinearIndependent.pair_iff] at hli
  obtain ⟨β₀, α₀, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one h₀
  obtain ⟨β₁, α₁, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one h₁
  have key : ∀ s t : K, s • (C β₀ * X + C α₀) + t • (C β₁ * X + C α₁) =
      C (s * β₀ + t * β₁) * X + C (s * α₀ + t * α₁) := fun s t => by
    simp only [smul_eq_C_mul, C_add, C_mul]; ring
  have hD : α₀ * β₁ - α₁ * β₀ ≠ 0 := by
    intro hD
    obtain ⟨-, hb₀⟩ := hli β₁ (-β₀) (by
      rw [key, show β₁ * β₀ + -β₀ * β₁ = 0 by ring,
        show β₁ * α₀ + -β₀ * α₁ = 0 by linear_combination hD]
      simp)
    obtain ⟨-, ha₀⟩ := hli α₁ (-α₀) (by
      rw [key, show α₁ * β₀ + -α₀ * β₁ = 0 by linear_combination -hD,
        show α₁ * α₀ + -α₀ * α₁ = 0 by ring]
      simp)
    exact one_ne_zero (hli 1 0 (by simp [neg_eq_zero.mp hb₀, neg_eq_zero.mp ha₀])).1
  refine ⟨?_, fun g hg => ?_⟩
  · by_cases h0 : β₀ = 0
    · exact Or.inr (natDegree_linear fun h1 => hD (by rw [h0, h1]; ring))
    · exact Or.inl (natDegree_linear h0)
  · obtain ⟨δ, γ, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hg
    obtain ⟨E, hE⟩ : ∃ E, E * (α₀ * β₁ - α₁ * β₀) = 1 := ⟨_, inv_mul_cancel₀ hD⟩
    refine ⟨(γ * β₁ - δ * α₁) * E, (α₀ * δ - β₀ * γ) * E, ?_⟩
    have h := key ((γ * β₁ - δ * α₁) * E) ((α₀ * δ - β₀ * γ) * E)
    rw [smul_eq_C_mul, smul_eq_C_mul,
      show (γ * β₁ - δ * α₁) * E * β₀ + (α₀ * δ - β₀ * γ) * E * β₁ = δ by
        linear_combination δ * hE,
      show (γ * β₁ - δ * α₁) * E * α₀ + (α₀ * δ - β₀ * γ) * E * α₁ = γ by
        linear_combination γ * hE] at h
    exact h.symm

end R4B_cubic

open DiazModulus R4B_cubic Polynomial in
theorem solution {K : Type*} [Field K] (P₀ P₁ P₂ : Polynomial K)
    (h₁ : P₁.natDegree ≤ 3) (h₂ : P₂.natDegree ≤ 3)
    (hli : LinearIndependent K ![P₀, P₁]) (hrel : P₁ * P₂ = P₀ ^ 2) :
    ∃ Q₀ Q₁ : Polynomial K, Q₀.natDegree ≤ 1 ∧ Q₁.natDegree ≤ 1 ∧
      LinearIndependent K ![Q₀, Q₁] ∧ ∃ a b : K,
        P₀ = (Polynomial.C a * Q₀ + Polynomial.C b * Q₁) * Q₀ * Q₁ ∧
        P₁ = (Polynomial.C a * Q₀ + Polynomial.C b * Q₁) * Q₁ ^ 2 ∧
        P₂ = (Polynomial.C a * Q₀ + Polynomial.C b * Q₁) * Q₀ ^ 2 := by
  have hP₀ : P₀ ≠ 0 := by simpa using hli.ne_zero 0
  have hP₁ : P₁ ≠ 0 := by simpa using hli.ne_zero 1
  -- 1. `P₀ = d Q₀`, `P₁ = d Q₁` with `Q₀, Q₁` coprime.
  obtain ⟨Q₀, Q₁, d, hrp, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors P₀ hP₀ P₁
  have hd : d ≠ 0 := left_ne_zero_of_mul hP₀
  have hQ₀ : Q₀ ≠ 0 := right_ne_zero_of_mul hP₀
  have hQ₁ : Q₁ ≠ 0 := right_ne_zero_of_mul hP₁
  -- 2. `d = Q₁ G`, and the three identities; degrees.
  have h3 : Q₁ * P₂ = d * Q₀ ^ 2 := mul_left_cancel₀ hd (by linear_combination hrel)
  have hdvd : Q₁ ∣ d * Q₀ ^ 2 := ⟨P₂, h3.symm⟩
  obtain ⟨g, rfl⟩ := hrp.isCoprime.symm.pow_right.dvd_of_dvd_mul_right hdvd
  have hg : g ≠ 0 := right_ne_zero_of_mul hd
  obtain rfl : P₂ = g * Q₀ ^ 2 := mul_left_cancel₀ hQ₁ (by linear_combination h3)
  rw [natDegree_mul (mul_ne_zero hQ₁ hg) hQ₁, natDegree_mul hQ₁ hg] at h₁
  rw [natDegree_mul hg (pow_ne_zero 2 hQ₀), natDegree_pow] at h₂
  -- 3. `Q₀, Q₁` are independent, and `G` is a combination of them.
  have hliQ : LinearIndependent K ![Q₀, Q₁] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    refine fun s t hst => hli s t ?_
    calc s • (Q₁ * g * Q₀) + t • (Q₁ * g * Q₁) = Q₁ * g * (s • Q₀ + t • Q₁) := by
          simp only [smul_eq_C_mul]; ring
      _ = 0 := by rw [hst, mul_zero]
  obtain ⟨hdeg, hspan⟩ := linear_pair (by omega) (by omega) hliQ
  obtain ⟨a, b, rfl⟩ := hspan g (by omega)
  exact ⟨Q₀, Q₁, by omega, by omega, hliQ, a, b, by ring, by ring, by ring⟩

#print axioms solution
