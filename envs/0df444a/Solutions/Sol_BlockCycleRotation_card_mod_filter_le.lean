-- Prove2me | solution 1 for BlockCycleRotation.card_mod_filter_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:24:52.706161+00:00
-- url     : https://prove2.me/submissions/64ccb24a-5ff5-4f3c-b947-d3b296726d5b

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
/-- **Counting a residue class in an interval.** -/
theorem solution {a U c : ℕ} (ha : 0 < a) :
    (((Finset.Ico 1 U).filter (fun b => b % a = c)).card) ≤ U / a + 1:= by
  classical
  have hmap : ∀ b ∈ (Finset.Ico 1 U).filter (fun b => b % a = c),
      b / a ∈ Finset.range (U / a + 1) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Ico] at hb
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : ∀ b₁ ∈ (Finset.Ico 1 U).filter (fun b => b % a = c),
      ∀ b₂ ∈ (Finset.Ico 1 U).filter (fun b => b % a = c), b₁ / a = b₂ / a → b₁ = b₂ := by
    intro b₁ h₁ b₂ h₂ heq
    simp only [Finset.mem_filter] at h₁ h₂
    have e₁ := Nat.div_add_mod b₁ a
    have e₂ := Nat.div_add_mod b₂ a
    rw [h₁.2] at e₁
    rw [h₂.2] at e₂
    rw [heq] at e₁
    omega
  calc (((Finset.Ico 1 U).filter (fun b => b % a = c)).card)
      ≤ (Finset.range (U / a + 1)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = U / a + 1 := Finset.card_range _
