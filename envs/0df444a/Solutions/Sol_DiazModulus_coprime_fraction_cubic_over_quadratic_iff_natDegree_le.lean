-- Prove2me | solution 1 for DiazModulus.coprime_fraction_cubic_over_quadratic_iff_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T09:49:57.019813+00:00
-- url     : https://prove2.me/submissions/92394820-f568-4612-a3b9-95ead2a2350d

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A coprime fraction `P/Q` equals `N/(X·R)` with `deg R ≤ 2`, `deg N ≤ 3` iff its degree is small

Let `K` be a field and `P, Q ∈ K[X]` coprime with `Q ≠ 0`.
* (⇒) From `X·R·P = N·Q` and `IsCoprime P Q`, `Q` divides `X·R`; write `X·R = Q·S`. Then
  `N = S·P` (cancel `Q`) and `S ≠ 0` (as `X·R ≠ 0`), so `deg Q + deg S = deg R + 1 ≤ 3` and
  `deg P + deg S ≤ 3` (or `P = 0`). If `Q(0) = 0` this already gives `max (deg P) (deg Q) ≤ 3`.
  If `Q(0) ≠ 0`, the prime `X` divides `Q·S` but not `Q`, so `X ∣ S` and `deg S ≥ 1`, which
  gives `max (deg P) (deg Q) ≤ 2`.
* (⇐) If `max ≤ 2` take `R = Q`, `N = X·P`. If `Q(0) = 0` and `max ≤ 3`, write `Q = X·Q₁` and
  take `R = Q₁`, `N = P`.
Mathlib: `IsCoprime.dvd_of_dvd_mul_right`, `Polynomial.natDegree_mul`, `Polynomial.natDegree_X_mul`,
`Polynomial.prime_X`, `Polynomial.X_dvd_iff`, `Polynomial.natDegree_le_of_dvd`. -/

namespace R17_frac

open Polynomial

theorem forward {K : Type*} [Field K] {P Q R N : K[X]} (hcop : IsCoprime P Q) (hQ : Q ≠ 0)
    (hR : R ≠ 0) (hR2 : R.natDegree ≤ 2) (hN3 : N.natDegree ≤ 3) (h : X * R * P = N * Q) :
    max P.natDegree Q.natDegree ≤ 2 ∨ (Q.coeff 0 = 0 ∧ max P.natDegree Q.natDegree ≤ 3) := by
  obtain ⟨S, hS⟩ : Q ∣ X * R := hcop.symm.dvd_of_dvd_mul_right ⟨N, by rw [h, mul_comm]⟩
  have hXR : X * R ≠ 0 := mul_ne_zero X_ne_zero hR
  have hS0 : S ≠ 0 := by rintro rfl; exact hXR (by rw [hS, mul_zero])
  have hN : N = S * P := by
    apply mul_right_cancel₀ hQ
    rw [← h, hS]; ring
  have hQS : Q.natDegree + S.natDegree ≤ 3 := by
    rw [← natDegree_mul hQ hS0, ← hS, natDegree_X_mul hR]; omega
  have hP3 : P.natDegree + S.natDegree ≤ 3 := by
    by_cases hP : P = 0
    · simp only [hP, natDegree_zero, zero_add]; omega
    · rw [add_comm, ← natDegree_mul hS0 hP, ← hN]; exact hN3
  by_cases hq0 : Q.coeff 0 = 0
  · right; refine ⟨hq0, ?_⟩; rw [max_le_iff]; omega
  · left
    have hXS : X ∣ S := by
      rcases prime_X.dvd_or_dvd (⟨R, hS.symm⟩ : X ∣ Q * S) with h1 | h1
      · exact absurd (X_dvd_iff.1 h1) hq0
      · exact h1
    have hS1 : 1 ≤ S.natDegree := by simpa using natDegree_le_of_dvd hXS hS0
    rw [max_le_iff]; omega

theorem backward {K : Type*} [Field K] {P Q : K[X]} (hQ : Q ≠ 0)
    (h : max P.natDegree Q.natDegree ≤ 2 ∨ (Q.coeff 0 = 0 ∧ max P.natDegree Q.natDegree ≤ 3)) :
    ∃ R N : K[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ X * R * P = N * Q := by
  rcases h with h | ⟨h0, h⟩
  · rw [max_le_iff] at h
    refine ⟨Q, X * P, hQ, h.2, ?_, by ring⟩
    calc (X * P).natDegree ≤ X.natDegree + P.natDegree := natDegree_mul_le
      _ ≤ 3 := by rw [natDegree_X]; omega
  · rw [max_le_iff] at h
    obtain ⟨Q₁, rfl⟩ := X_dvd_iff.2 h0
    have hQ₁ : Q₁ ≠ 0 := by rintro rfl; exact hQ (mul_zero _)
    rw [natDegree_X_mul hQ₁] at h
    exact ⟨Q₁, P, hQ₁, by omega, h.1, by ring⟩

end R17_frac

open DiazModulus Polynomial R17_frac in
theorem solution (K : Type*) [Field K] (P Q : K[X])
    (hcop : IsCoprime P Q) (hQ : Q ≠ 0) :
    (∃ R N : K[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ X * R * P = N * Q) ↔
      (max P.natDegree Q.natDegree ≤ 2 ∨ (Q.coeff 0 = 0 ∧ max P.natDegree Q.natDegree ≤ 3)) := by
  constructor
  · rintro ⟨R, N, hR, hR2, hN3, h⟩
    exact forward hcop hQ hR hR2 hN3 h
  · exact backward hQ
