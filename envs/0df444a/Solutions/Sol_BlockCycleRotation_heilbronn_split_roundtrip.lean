-- Prove2me | solution 1 for BlockCycleRotation.heilbronn_split_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:59:54.979332+00:00
-- url     : https://prove2.me/submissions/83628fa8-5a1d-4dd3-802b-37a1b4a3977e

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_reverse
import Theorems.Thm_BlockCycleRotation_cf_K
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

/-- Dropping the last entry of a reversed list drops the first entry. -/
theorem reverse_dropLast_eq (l : List ℕ) : (l.reverse).dropLast = (l.tail).reverse := by
  rcases l with _ | ⟨a, t⟩ <;> simp

/-- A prefix inherits the head condition. -/
theorem head_opt_take_of_head_opt {L : List ℕ} {j : ℕ} (hj : 1 ≤ j)
    (hhead : ∀ x ∈ L.head?, 2 ≤ x) : ∀ x ∈ (L.take j).head?, 2 ≤ x := by
  intro x hx
  apply hhead
  rcases L with _ | ⟨a, t⟩
  · simp at hx
  · rcases j with _ | j'
    · omega
    · simp at hx ⊢
      omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **The round trip on a split.**  For a normalised expansion `L` and an
interior split point, both halves are recovered from their continuants — the
prefix directly, the suffix after reversing.  This is what makes the passage
from splits to quadruples injective. -/
theorem solution {L : List ℕ} (hpos : ∀ c ∈ L, 1 ≤ c)
    (hhead : ∀ x ∈ L.head?, 2 ≤ x) (hlast : ∀ x ∈ L.getLast?, 2 ≤ x)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j < L.length) :
    cf (K (L.take j)) (K (L.take j).dropLast) = L.take j
      ∧ cf (K (L.drop j)) (K (L.drop j).tail) = (L.drop j).reverse:= by
  have hL : L ≠ [] := by
    intro hc
    rw [hc] at hj2
    simp at hj2
  -- the prefix inherits the head condition
  have hne₁ : L.take j ≠ [] := by
    intro hc
    have : (L.take j).length = 0 := by rw [hc]; simp
    rw [List.length_take] at this
    omega
  have hpos₁ : ∀ c ∈ L.take j, 1 ≤ c := fun c hc => hpos c (List.take_subset j L hc)
  have hhead₁ : ∀ x ∈ (L.take j).head?, 2 ≤ x := head_opt_take_of_head_opt hj1 hhead
  -- the reversed suffix inherits the last-entry condition as a head condition
  have hne₂ : (L.drop j).reverse ≠ [] := by
    intro hc
    have : (L.drop j).length = 0 := by
      have := congrArg List.length hc
      simpa using this
    rw [List.length_drop] at this
    omega
  have hpos₂ : ∀ c ∈ (L.drop j).reverse, 1 ≤ c := by
    intro c hc
    exact hpos c (List.drop_subset j L (List.mem_reverse.1 hc))
  have hdropne : L.drop j ≠ [] := by
    intro hc
    have hl : (L.drop j).length = 0 := by rw [hc]; simp
    rw [List.length_drop] at hl
    omega
  have hgl : L.getLast? = (L.drop j).getLast? := by
    conv_lhs => rw [← List.take_append_drop j L]
    exact List.getLast?_append_of_ne_nil _ hdropne
  have hhead₂ : ∀ x ∈ ((L.drop j).reverse).head?, 2 ≤ x := by
    intro x hx
    rw [List.head?_reverse, ← hgl] at hx
    exact hlast x hx
  refine ⟨cf_K _ hne₁ hpos₁ hhead₁, ?_⟩
  have h := cf_K _ hne₂ hpos₂ hhead₂
  rwa [K_reverse, reverse_dropLast_eq, K_reverse] at h
