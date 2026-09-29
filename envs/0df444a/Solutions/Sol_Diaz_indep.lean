-- Prove2me | solution 1 for Diaz.indep
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:14.097524+00:00
-- url     : https://prove2.me/submissions/b2282c26-a2de-46c0-82b0-99b3b22ade5b

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
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

/-- If `t` is transcendental over `K` and `ρ = t · conj t` lies in `K`,
then the cross term `t² + conj(t)²` does not lie in `K`.

Otherwise `t` would satisfy `X⁴ - c X² + ρ²`, a non-zero polynomial over
`K`. This is what forces `a b = 0` in the model. -/
theorem sq_add_sq_notMem (hT : Transcendental K t) (hρ : t * conj t ∈ K) :
    t ^ 2 + (conj t) ^ 2 ∉ K := by
  intro hc
  refine hT ?_
  refine ⟨X ^ 4 - C (⟨_, hc⟩ : K) * X ^ 2 + C (⟨_, hρ⟩ : K) ^ 2, ?_, ?_⟩
  · have : (X ^ 4 - C (⟨_, hc⟩ : K) * X ^ 2 + C (⟨_, hρ⟩ : K) ^ 2).Monic := by
      monicity!
    exact this.ne_zero
  · simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
    show t ^ 4 - (t ^ 2 + (conj t) ^ 2) * t ^ 2 + (t * conj t) ^ 2 = 0
    ring
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
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

open Diaz in
theorem solution (hT : Transcendental K t) (hρ : t * conj t ∈ K)
    {a b : ℚ} (h : (a : ℂ) * t + (b : ℂ) * conj t = 0) : a = 0 ∧ b = 0 := by
  have ht0 : t ≠ 0 := transcendental_ne_zero hT
  have hc : conj t = (t * conj t) / t := (conj_eq_rho_div ht0).symm
  have hρ0 : t * conj t ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨ht0, by simpa using ht0⟩
  by_cases ha : a = 0
  · refine ⟨ha, ?_⟩
    rw [ha] at h
    simp only [Rat.cast_zero, zero_mul, zero_add, mul_eq_zero] at h
    rcases h with h | h
    · exact_mod_cast h
    · exact absurd h (by simpa using ht0)
  · exfalso
    -- `a t² + b ρ = 0` with `a ≠ 0` makes `t²`, hence `t`, algebraic over `K`
    refine sq_add_sq_notMem hT hρ ?_
    have key : (t : ℂ) ^ 2 = -((b : ℂ) / (a : ℂ)) * (t * conj t) := by
      rw [hc] at h
      field_simp at h ⊢
      linear_combination h
    have hK2 : (t : ℂ) ^ 2 ∈ K := by
      rw [key]
      exact mul_mem (neg_mem (div_mem (by simp) (by simp))) hρ
    have : (conj t) ^ 2 ∈ K := by
      have : (conj t) ^ 2 = (t * conj t) ^ 2 / t ^ 2 := by
        rw [hc]; field_simp
      rw [this]
      exact div_mem (pow_mem hρ 2) hK2
    exact add_mem hK2 this
end
