-- Prove2me | solution 1 for BlockCycleRotation.card_a_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:21:48.824075+00:00
-- url     : https://prove2.me/submissions/bc538d28-e6e2-4ca8-9866-e8ec30cdcdcc

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
/-- The admissible `a` are at most `√((m-1)/d)`. -/
theorem solution {m d : ℕ} (hd : 0 < d) :
    ((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card
      ≤ Nat.sqrt ((m - 1) / d) + 1:= by
  have hsub : (Finset.range (m + 1)).filter (fun a => d * a * a < m)
      ⊆ Finset.range (Nat.sqrt ((m - 1) / d) + 1) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    obtain ⟨-, hda⟩ := ha
    have h1 : a * a * d ≤ m - 1 := by
      have heq : d * a * a = a * a * d := by ring
      omega
    exact Nat.lt_succ_of_le (Nat.le_sqrt.2 ((Nat.le_div_iff_mul_le hd).2 h1))
  calc ((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card
      ≤ (Finset.range (Nat.sqrt ((m - 1) / d) + 1)).card := Finset.card_le_card hsub
    _ = Nat.sqrt ((m - 1) / d) + 1 := Finset.card_range _
