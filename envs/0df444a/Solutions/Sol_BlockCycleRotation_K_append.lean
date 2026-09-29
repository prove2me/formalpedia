-- Prove2me | solution 1 for BlockCycleRotation.K_append
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:43:17.507116+00:00
-- url     : https://prove2.me/submissions/134dbbc2-cea7-4a5e-a668-de2eaf282bac

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
/-- **Euler's continuant identity.**  Splitting a list at any interior point,

  `K (l₁ ++ l₂) = K l₁ · K l₂ + K (l₁.dropLast) · K (l₂.tail)`.

This is the identity that turns a split continued-fraction expansion into a
solution of `n = a·b + a'·b'`. -/
theorem solution : ∀ (l₁ l₂ : List ℕ), l₁ ≠ [] → l₂ ≠ [] →
    K (l₁ ++ l₂) = K l₁ * K l₂ + K l₁.dropLast * K l₂.tail:= by
  intro l₁
  induction l₁ using K.induct with
  | case1 => intro _ h; exact absurd rfl h
  | case2 c =>
    intro l₂ _ h₂
    match l₂, h₂ with
    | d :: ds, _ =>
      simp [K_cons_cons]
  | case3 c₀ c₁ cs ih1 ih2 =>
    intro l₂ _ h₂
    rcases cs with _ | ⟨c₂, cs'⟩
    · -- `l₁ = [c₀, c₁]`
      match l₂, h₂ with
      | d :: ds, _ =>
        simp [K_cons_cons]
        ring
    · -- `cs` is nonempty, so both inductive hypotheses apply
      have hcs : (c₂ :: cs') ≠ [] := by simp
      have h1 := ih1 l₂ (by simp) h₂
      have h2 := ih2 l₂ hcs h₂
      simp only [List.cons_append, K_cons_cons, List.dropLast_cons_cons] at *
      rw [h1, h2]
      ring
