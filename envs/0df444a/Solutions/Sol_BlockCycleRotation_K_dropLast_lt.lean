-- Prove2me | solution 1 for BlockCycleRotation.K_dropLast_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:48:43.559303+00:00
-- url     : https://prove2.me/submissions/f5833215-918f-41bf-8063-c888178c8b02

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Theorems.Thm_BlockCycleRotation_K_pos
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

/-- The mirrored recursion: appending an entry at the end. -/
theorem K_concat (l : List ℕ) (h : l ≠ []) (c : ℕ) :
    K (l ++ [c]) = c * K l + K l.dropLast := by
  rw [K_append l [c] h (by simp)]
  simp [Nat.mul_comm]

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- Dropping the last entry strictly decreases the continuant, provided at least
two entries remain in play. -/
theorem solution : ∀ l : List ℕ, 2 ≤ l.length → (∀ c ∈ l, 1 ≤ c) →
    K l.dropLast < K l:= by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro h _; simp at h
  | append_singleton m c _ =>
    intro hlen hpos
    have hm : m ≠ [] := by
      rintro rfl
      simp at hlen
    have hdl : (m ++ [c]).dropLast = m := by simp
    have hsub : ∀ x ∈ m, x ∈ m ++ [c] := fun x hx => List.mem_append.2 (Or.inl hx)
    have hc1 : 1 ≤ c := hpos c (by simp)
    have hmp : 1 ≤ K m := K_pos m (fun x hx => hpos x (hsub x hx))
    have hmd : 1 ≤ K m.dropLast :=
      K_pos _ (fun x hx => hpos x (hsub x (List.dropLast_subset m hx)))
    rw [K_concat m hm c, hdl]
    nlinarith
