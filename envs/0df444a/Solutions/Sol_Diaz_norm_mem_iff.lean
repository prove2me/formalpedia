-- Prove2me | solution 1 for Diaz.norm_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:16.142337+00:00
-- url     : https://prove2.me/submissions/d14e295c-312a-45ef-a91e-f4f0952b2367

import Mathlib

namespace Diaz

section
open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

/-- On the rational plane spanned by `t` and `conj t`,

    (a t + b t̄)(a t̄ + b t) = (a² + b²)·t t̄ + a b·(t² + t̄²).

This is `x σ(x) = (a² + b²) ρ + a b (T² + ρ²/T²)` of `prop:model`, with
`conj` in place of `σ`. -/
theorem norm_form (t : ℂ) (a b : ℚ) :
    ((a : ℂ) * t + (b : ℂ) * conj t) * conj ((a : ℂ) * t + (b : ℂ) * conj t)
      = ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (t * conj t)
        + ((a : ℂ) * (b : ℂ)) * (t ^ 2 + (conj t) ^ 2) := by
  simp only [map_add, map_mul, Complex.conj_conj, map_ratCast]
  ring
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

end Diaz

section
open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

open Diaz in
theorem solution (hT : Transcendental K t) (hρ : t * conj t ∈ K) (a b : ℚ) :
    ((a : ℂ) * t + (b : ℂ) * conj t) * conj ((a : ℂ) * t + (b : ℂ) * conj t) ∈ K
      ↔ a = 0 ∨ b = 0 := by
  have hQ : ∀ q : ℚ, (q : ℂ) ∈ K := fun q => by
    simp
  constructor
  · intro hmem
    by_contra hab
    rw [not_or] at hab
    obtain ⟨ha, hb⟩ := hab
    refine sq_add_sq_notMem hT hρ ?_
    have hab0 : ((a : ℂ) * (b : ℂ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Rat.cast_eq_zero]
      tauto
    have hcross : ((a : ℂ) * (b : ℂ)) * (t ^ 2 + (conj t) ^ 2) ∈ K := by
      have := norm_form t a b
      rw [this] at hmem
      have hfirst : ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (t * conj t) ∈ K :=
        mul_mem (add_mem (pow_mem (hQ a) 2) (pow_mem (hQ b) 2)) hρ
      simpa using sub_mem hmem hfirst
    have := div_mem hcross (mul_mem (hQ a) (hQ b))
    rwa [mul_div_cancel_left₀ _ hab0] at this
  · intro h
    rw [norm_form]
    refine add_mem (mul_mem (add_mem (pow_mem (hQ a) 2) (pow_mem (hQ b) 2)) hρ) ?_
    rcases h with rfl | rfl <;>
      simp only [Rat.cast_zero, zero_mul, mul_zero, zero_mem]
end
