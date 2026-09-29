-- Prove2me | solution 1 for Diaz.four_nodes
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:13.601864+00:00
-- url     : https://prove2.me/submissions/2d62a503-50db-4fb2-8c59-b1ca70913a9a

import Mathlib

namespace Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

/-- `v · conj v = (a-b)²ρ + ab(u + conj u)²` for `v = a u + b conj u`.

The note writes the second term as `4ab(Re u)²`, the same thing since
`u + conj u = 2 Re u`. -/
theorem plane_norm (u : ℂ) (a b : ℚ) :
    ((a : ℂ) * u + (b : ℂ) * conj u) * conj ((a : ℂ) * u + (b : ℂ) * conj u)
      = ((a : ℂ) - (b : ℂ)) ^ 2 * (u * conj u)
        + (a : ℂ) * (b : ℂ) * (u + conj u) ^ 2 := by
  simp only [map_add, map_mul, Complex.conj_conj, map_ratCast]
  ring
end

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

open Diaz in
theorem solution (hρ : u * conj u ∈ K) (hre : (u + conj u) ^ 2 ∉ K)
    {a b : ℚ} (h : ((a : ℂ) * u + (b : ℂ) * conj u)
      * conj ((a : ℂ) * u + (b : ℂ) * conj u) = u * conj u) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0)
      ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  rw [plane_norm] at h
  have hQ : ∀ q : ℚ, (q : ℂ) ∈ K := fun q => by simp
  -- `u * conj u` is non-zero, else `u = 0` and the cross term lies in `K`
  have hρ0 : u * conj u ≠ 0 := by
    intro hc
    refine hre ?_
    have hu0 : u = 0 := by
      rcases mul_eq_zero.mp hc with h' | h'
      · exact h'
      · simpa using congrArg (starRingEnd ℂ) h'
    rw [hu0]
    simp
  -- the cross term must vanish, else `(u + conj u)²` would lie in `K`
  have hab : a * b = 0 := by
    by_contra hne
    refine hre ?_
    have hne' : ((a : ℂ) * (b : ℂ)) ≠ 0 := by
      simpa using (Rat.cast_ne_zero (α := ℂ)).mpr hne
    have hstep : (u + conj u) ^ 2
        = (1 - ((a : ℂ) - (b : ℂ)) ^ 2) * (u * conj u) / ((a : ℂ) * (b : ℂ)) := by
      rw [eq_div_iff hne']
      linear_combination h
    rw [hstep]
    exact div_mem (mul_mem (sub_mem (one_mem K)
      (pow_mem (sub_mem (hQ a) (hQ b)) 2)) hρ) (mul_mem (hQ a) (hQ b))
  -- and then `(a - b)² = 1`
  have hsq : (a - b) ^ 2 = 1 := by
    have hz : ((a : ℂ) * (b : ℂ)) = 0 := by exact_mod_cast hab
    rw [hz, zero_mul, add_zero] at h
    have : ((a : ℂ) - (b : ℂ)) ^ 2 = 1 := mul_right_cancel₀ hρ0 (by rw [h, one_mul])
    exact_mod_cast this
  rcases mul_eq_zero.mp hab with ha | hb
  · subst ha
    have : (b - 1) * (b + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp this with h' | h'
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, by linarith⟩))
  · subst hb
    have : (a - 1) * (a + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp this with h' | h'
    · exact Or.inl ⟨by linarith, rfl⟩
    · exact Or.inr (Or.inl ⟨by linarith, rfl⟩)
end
