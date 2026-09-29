-- Prove2me | solution 1 for BlockCycleRotation.quadExpansion_shift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:01:23.779485+00:00
-- url     : https://prove2.me/submissions/5f75359e-0a16-461d-a0d6-78f00bb98f29

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_coprime
import Theorems.Thm_BlockCycleRotation_K_pos
import Theorems.Thm_BlockCycleRotation_cf_K
import Theorems.Thm_BlockCycleRotation_two_mul_K_dropLast_le
import Theorems.Thm_BlockCycleRotation_quadExpansion_spec
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

theorem mem_shifts {n k : ℕ} :
    k ∈ shifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1 := by
  simp [shifts]

end BlockCycleRotation

open BlockCycleRotation in
/-- The shift attached to a quadruple lies in `shifts n`, and its expansion is
the reassembled one. -/
theorem solution {n a b a' b' : ℕ} (hq : (a, b, a', b') ∈ quadruples n) :
    K (quadExpansion a b a' b').dropLast ∈ shifts n
      ∧ cf n (K (quadExpansion a b a' b').dropLast) = quadExpansion a b a' b':= by
  obtain ⟨hKL, hne, hpos, hhead, hlast, -, -, -, -⟩ := quadExpansion_spec hq
  set L := quadExpansion a b a' b' with hL
  have hk1 : 1 ≤ K L.dropLast :=
    K_pos _ (fun x hx => hpos x (List.dropLast_subset L hx))
  have hk2 : 2 * K L.dropLast ≤ n := by
    have := two_mul_K_dropLast_le L hne hpos hlast
    omega
  have hgcd : Nat.gcd n (K L.dropLast) = 1 := by
    rw [← hKL]
    exact K_coprime L
  refine ⟨mem_shifts.2 ⟨by omega, hk1, hk2, hgcd⟩, ?_⟩
  have := cf_K L hne hpos hhead
  rwa [hKL] at this
