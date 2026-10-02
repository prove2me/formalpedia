-- Prove2me | solution 1 for DiazModulus.diaz_2007_cor7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:35:45.773984+00:00
-- url     : https://prove2.me/submissions/b0f28dd0-be2e-4e32-af09-8b4e40a842b3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_diaz_2007_th5

/-!
# Diaz 2007, Corollaire 7

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres
algébriques*, JTNB 19 (2007), Corollaire 7 (pp. 385–388).

Théorème 5 2) (`DiazModulus.diaz_2007_th5`) applied to `u ∈ ℒ̃` and `v`, with `w = 2πi ∈ ℒ`
(`exp (2πi) = 1`). Since `im τ > 0`, neither `τ` nor `1/τ` is rational, and `τ ≠ 0`.

* If `τ ∈ ℒ̃`: `u = τ`, `v = w/τ`. The products `v = w/τ`, `vu = w`, `vu² = wτ` all lie in `ℒ`.
* If `1/τ ∈ ℒ̃`: `u = 1/τ`, `v = wτ`. The products `v = wτ`, `vu = w`, `vu² = w/τ` all lie in `ℒ`.

Here `e^{wτ}` algebraic means `wτ ∈ ℒ`, and `e^{-w/τ}` algebraic means `-w/τ ∈ ℒ`, hence
`w/τ ∈ ℒ`, as `ℒ` is closed under negation.
-/

open Complex ComplexConjugate

namespace D6_diaz_2007_cor7

open DiazModulus

/-- `ℒ` is closed under negation: `exp (-z) = (exp z)⁻¹`. -/
theorem neg_mem_logAlg {z : ℂ} (h : z ∈ LogAlg) : -z ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (-z))
  rw [Complex.exp_neg]
  exact IsAlgebraic.inv h

/-- `2πi ∈ ℒ`, since `exp (2πi) = 1`. -/
theorem two_pi_I_mem_logAlg : 2 * ((Real.pi : ℝ) : ℂ) * Complex.I ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))
  rw [Complex.exp_two_pi_mul_I]
  exact isAlgebraic_one

/-- A complex number with non-zero imaginary part is not rational. -/
theorem ne_ratCast_of_im_ne_zero {z : ℂ} (h : z.im ≠ 0) : ∀ q : ℚ, z ≠ q := by
  intro q hq
  apply h
  rw [hq, Complex.ratCast_im]

end D6_diaz_2007_cor7

open DiazModulus D6_diaz_2007_cor7 in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    ∀ τ : ℂ, 0 < τ.im → (τ ∈ LogAlgTilde ∨ 1 / τ ∈ LogAlgTilde) →
      ¬ (IsAlgebraic ℚ (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ)) ∧
        IsAlgebraic ℚ (Complex.exp (-(2 * ((Real.pi : ℝ) : ℂ) * Complex.I) / τ))) := by
  obtain ⟨-, th2⟩ := diaz_2007_th5 hSSE hB
  intro τ hτ hmem ⟨hA, hA'⟩
  have hτ0 : τ ≠ 0 := fun h => by
    rw [h, Complex.zero_im] at hτ
    exact lt_irrefl 0 hτ
  have hw0 := Complex.two_pi_I_ne_zero
  have hwL := two_pi_I_mem_logAlg
  set w : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * Complex.I
  -- `wτ ∈ ℒ` and `w/τ ∈ ℒ`
  have hwτ : w * τ ∈ LogAlg := hA
  have hwdiv : w / τ ∈ LogAlg := by
    have h := neg_mem_logAlg (z := -w / τ) hA'
    rwa [neg_div, neg_neg] at h
  rcases hmem with hτL | hτL
  · -- `u = τ`, `v = w/τ`: the products are `w/τ`, `w`, `wτ`
    refine th2 τ (w / τ) (ne_ratCast_of_im_ne_zero hτ.ne') (div_ne_zero hw0 hτ0) hτL
      ⟨hwdiv, ?_, ?_⟩
    · rwa [div_mul_cancel₀ w hτ0]
    · have e : w / τ * τ ^ 2 = w * τ := by
        field_simp
      rwa [e]
  · -- `u = 1/τ`, `v = wτ`: the products are `wτ`, `w`, `w/τ`
    have him : (1 / τ).im ≠ 0 := by
      rw [one_div, Complex.inv_im]
      exact div_ne_zero (neg_ne_zero.2 hτ.ne') (Complex.normSq_pos.2 hτ0).ne'
    refine th2 (1 / τ) (w * τ) (ne_ratCast_of_im_ne_zero him) (mul_ne_zero hw0 hτ0) hτL
      ⟨hwτ, ?_, ?_⟩
    · have e : w * τ * (1 / τ) = w := by
        field_simp
      rwa [e]
    · have e : w * τ * (1 / τ) ^ 2 = w / τ := by
        field_simp
      rwa [e]
