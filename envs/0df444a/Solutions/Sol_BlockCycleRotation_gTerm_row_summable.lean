-- Prove2me | solution 1 for BlockCycleRotation.gTerm_row_summable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:39:40.930552+00:00
-- url     : https://prove2.me/submissions/71182792-b2cb-4d07-abdb-c09af54c2b88

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open Real Finset Filter Topology

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

theorem gTerm_row_support (a a' : ℕ) (h : a' ∉ Finset.range a) : gTerm (a, a') = 0 := by
  simp only [Finset.mem_range, not_lt] at h
  unfold gTerm
  rw [if_neg]
  rintro ⟨-, h2⟩
  omega

end BlockCycleRotation

open BlockCycleRotation in
theorem solution (a : ℕ) : Summable (fun a' => gTerm (a, a')):=
  summable_of_ne_finset_zero (s := Finset.range a) (gTerm_row_support a)
