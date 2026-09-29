-- Prove2me | solution 1 for BlockCycleRotation.K_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:45:20.601048+00:00
-- url     : https://prove2.me/submissions/ada71095-5cc2-4bea-a4bf-b38f558337c8

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

theorem K_cons_cons (c₀ c₁ : ℕ) (cs : List ℕ) :
    K (c₀ :: c₁ :: cs) = c₀ * K (c₁ :: cs) + K cs := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- Continuants of lists of positive entries are positive. -/
theorem solution : ∀ l : List ℕ, (∀ c ∈ l, 1 ≤ c) → 1 ≤ K l:= by
  intro l
  induction l using K.induct with
  | case1 => intro _; simp
  | case2 c => intro h; exact h c (by simp)
  | case3 c₀ c₁ cs ih1 ih2 =>
    intro h
    have h1 := ih1 (fun x hx => h x (List.mem_cons_of_mem c₀ hx))
    have h2 := ih2 (fun x hx => h x (List.mem_cons_of_mem c₀ (List.mem_cons_of_mem c₁ hx)))
    have hc0 : 1 ≤ c₀ := h c₀ (by simp)
    rw [K_cons_cons]
    nlinarith
