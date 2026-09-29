-- Prove2me | solution 1 for BlockCycleRotation.K_reverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:44:39.059135+00:00
-- url     : https://prove2.me/submissions/bf93ff16-5fd8-4239-ad0a-292c5fd28950

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
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

theorem K_cons_cons (c₀ c₁ : ℕ) (cs : List ℕ) :
    K (c₀ :: c₁ :: cs) = c₀ * K (c₁ :: cs) + K cs := rfl

/-- The mirrored recursion: appending an entry at the end. -/
theorem K_concat (l : List ℕ) (h : l ≠ []) (c : ℕ) :
    K (l ++ [c]) = c * K l + K l.dropLast := by
  rw [K_append l [c] h (by simp)]
  simp [Nat.mul_comm]

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Continuants are palindromic**: `K` is invariant under reversing the list.

This is what lets Heilbronn's bijection read the second half of the expansion
backwards. -/
theorem solution : ∀ l : List ℕ, K l.reverse = K l:= by
  intro l
  induction l using K.induct with
  | case1 => simp
  | case2 c => simp
  | case3 c₀ c₁ cs ih1 ih2 =>
    have hne : ((c₁ :: cs).reverse) ≠ [] := by simp
    have hdrop : ((c₁ :: cs).reverse).dropLast = cs.reverse := by
      rw [List.reverse_cons]
      simp
    rw [List.reverse_cons, K_concat _ hne c₀, ih1, hdrop, ih2, K_cons_cons]
