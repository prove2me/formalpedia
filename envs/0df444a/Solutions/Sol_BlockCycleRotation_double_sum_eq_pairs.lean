-- Prove2me | solution 1 for BlockCycleRotation.double_sum_eq_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:18:50.081779+00:00
-- url     : https://prove2.me/submissions/49350cef-fd64-4de3-9392-01a85e49ee7a

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The double sum as a sum over pairs. -/
theorem solution {N : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, f a a'
      = ∑ p ∈ ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter (fun p => p.2 < p.1),
          f p.1 p.2:= by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (i := fun x _ => (x.1, x.2))
    (j := fun p _ => (⟨p.1, p.2⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, a'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hx.1, by omega⟩, hx.2⟩
  · rintro ⟨a, a'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨hp.1.1, hp.2⟩
  · rintro ⟨a, a'⟩ _; rfl
  · rintro ⟨a, a'⟩ _; rfl
  · rintro ⟨a, a'⟩ _; rfl
