-- Prove2me | solution 1 for DiazModulus.rank_one_polynomial_matrix_factor
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T14:04:57.498808+00:00
-- url     : https://prove2.me/submissions/77e6eddc-dc16-4b3f-a0cf-6c745a7475a5

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A rank-one `2 × 3` polynomial matrix factors with a coprime column

Let `P` be a `2 × 3` matrix over `F[X]` with non-zero entries whose `2 × 2` minors all vanish.
Since `F[X]` is a Euclidean domain, put `g = gcd(P₀₀, P₁₀)` and `aᵢ = Pᵢ₀ / g`; the division is
exact and `a₀`, `a₁` are coprime. The minor on columns `0` and `j` reads
`P₀ⱼ P₁₀ = P₀₀ P₁ⱼ`, that is `g (a₁ P₀ⱼ) = g (a₀ P₁ⱼ)`, and cancelling `g ≠ 0` gives
`a₁ P₀ⱼ = a₀ P₁ⱼ`. By coprimality `a₀ ∣ P₀ⱼ`; write `P₀ⱼ = a₀ bⱼ`. Then
`a₀ P₁ⱼ = a₁ a₀ bⱼ`, and cancelling `a₀ ≠ 0` gives `P₁ⱼ = a₁ bⱼ`. So `Pᵢⱼ = aᵢ bⱼ` throughout.
-/

open DiazModulus Polynomial in
theorem solution (F : Type*) [Field F] (P : Fin 2 → Fin 3 → F[X])
    (hP : ∀ i j, P i j ≠ 0)
    (hminor : ∀ i i' j j', P i j * P i' j' = P i j' * P i' j) :
    ∃ (a : Fin 2 → F[X]) (b : Fin 3 → F[X]), IsCoprime (a 0) (a 1) ∧ ∀ i j, P i j = a i * b j := by
  classical
  set g := GCDMonoid.gcd (P 0 0) (P 1 0)
  have hg0 : g ≠ 0 := gcd_ne_zero_of_left (hP 0 0)
  set a₀ := P 0 0 / g
  set a₁ := P 1 0 / g
  have hcop : IsCoprime a₀ a₁ := isCoprime_div_gcd_div_gcd (hP 1 0)
  have h₀ : g * a₀ = P 0 0 := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)
  have h₁ : g * a₁ = P 1 0 := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)
  have ha₀ : a₀ ≠ 0 := fun h => hP 0 0 (by rw [← h₀, h, mul_zero])
  have hrel : ∀ j, a₁ * P 0 j = a₀ * P 1 j := fun j =>
    mul_left_cancel₀ hg0 (by linear_combination hminor 0 1 j 0 + P 0 j * h₁ - P 1 j * h₀)
  choose b hb using fun j => hcop.dvd_of_dvd_mul_left ⟨P 1 j, hrel j⟩
  refine ⟨![a₀, a₁], b, hcop, fun i j => ?_⟩
  fin_cases i
  · exact hb j
  · refine mul_left_cancel₀ ha₀ ?_
    change a₀ * P 1 j = a₀ * (a₁ * b j)
    rw [← hrel j, hb j]
    ring
