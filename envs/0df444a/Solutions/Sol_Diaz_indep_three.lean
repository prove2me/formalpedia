-- Prove2me | solution 1 for Diaz.indep_three
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:14.644251+00:00
-- url     : https://prove2.me/submissions/33f863e1-05df-4f75-b950-6a198954718a

import Mathlib

namespace Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- With `ρ = u * conj u`, the conjugate of `u` is `ρ / u`.

Trivial as algebra, and it is the entire content of the closure theorem:
`conj u` is not an independent quantity but a rational function of `u`
over the base field.  Everything else follows. -/
theorem conj_eq_rho_div (hu : u ≠ 0) : (u * conj u) / u = conj u := by
  field_simp
end

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- A transcendental element is non-zero: `0` is a root of `X`. -/
theorem transcendental_ne_zero {F : Type*} [Field F] [Algebra F ℂ] {z : ℂ}
    (h : Transcendental F z) : z ≠ 0 := by
  rintro rfl
  exact h isAlgebraic_zero
end

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

open Diaz in
theorem solution (hT : Transcendental K u) (hρ : u * conj u ∈ K)
    {a b c : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (h : a + b * u + c * conj u = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hu0 : u ≠ 0 := transcendental_ne_zero hT
  have hρ0 : u * conj u ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨hu0, by simpa using hu0⟩
  -- substituting conj u = (u conj u)/u and clearing gives a quadratic over K
  have hquad : b * u ^ 2 + a * u + c * (u * conj u) = 0 := by
    have hcu : conj u = (u * conj u) / u := (conj_eq_rho_div hu0).symm
    rw [hcu] at h
    field_simp at h
    linear_combination u * h
  by_contra hne
  refine hT ⟨Polynomial.C (⟨b, hb⟩ : K) * Polynomial.X ^ 2
      + Polynomial.C (⟨a, ha⟩ : K) * Polynomial.X
      + Polynomial.C (⟨c * (u * conj u), mul_mem hc hρ⟩ : K), ?_, ?_⟩
  · -- the polynomial is non-zero: otherwise every coefficient is, and then so is (a,b,c)
    intro hzero
    apply hne
    have hb0 : b = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 2) hzero
      simpa using congrArg (Subtype.val) this
    have ha0 : a = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 1) hzero
      simpa using congrArg (Subtype.val) this
    have hc0 : c = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 0) hzero
      have h0 : c * (u * conj u) = 0 := by simpa using congrArg (Subtype.val) this
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact h'
      · exact absurd h' hρ0
    exact ⟨ha0, hb0, hc0⟩
  · simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    show b * u ^ 2 + a * u + c * (u * conj u) = 0
    exact hquad
end
