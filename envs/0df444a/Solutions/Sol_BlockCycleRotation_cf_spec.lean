-- Prove2me | solution 1 for BlockCycleRotation.cf_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:53:08.534058+00:00
-- url     : https://prove2.me/submissions/1643f8f9-4372-42b9-a7d7-5c3072a10da1

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

theorem cf_of_pos {a a' : ℕ} (h : a' ≠ 0) :
    cf a a' = cf a' (a % a') ++ [a / a'] := by rw [cf]; simp [h]

end BlockCycleRotation

open BlockCycleRotation in
/-- The expansion produced by `cf` is normalised: nonempty, with positive
entries and first entry at least `2`. -/
theorem solution : ∀ a' a : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
    cf a a' ≠ [] ∧ (∀ x ∈ cf a a', 1 ≤ x) ∧ (∀ x ∈ (cf a a').head?, 2 ≤ x):= by
  intro a'
  induction a' using Nat.strong_induction_on with
  | _ a' ih =>
    intro a ha'1 hlt hgcd
    rcases Nat.lt_or_ge a' 2 with h2 | h2
    · have ha'eq : a' = 1 := by omega
      subst ha'eq
      have h1 : cf a 1 = [a] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [h1]
      refine ⟨by simp, ?_, ?_⟩ <;> intro x hx <;> simp at hx <;> omega
    · have ha'ne : a' ≠ 0 := by omega
      have hrlt : a % a' < a' := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ a % a' := by
        rcases Nat.eq_zero_or_pos (a % a') with h0 | h0
        · exfalso
          have hg : Nat.gcd a a' = a' := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h0)
          omega
        · exact h0
      have hgcd' : Nat.gcd a' (a % a') = 1 := by
        rw [← hgcd, Nat.gcd_comm a a', Nat.gcd_rec a' a]
        exact Nat.gcd_comm _ _
      obtain ⟨hne, hpos, hhd⟩ := ih (a % a') hrlt a' hr1 hrlt hgcd'
      have hq1 : 1 ≤ a / a' := (Nat.one_le_div_iff (by omega)).2 (by omega)
      rw [cf_of_pos ha'ne]
      refine ⟨by simp, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hpos x h
        · simp at h; omega
      · intro x hx
        rcases hcf : cf a' (a % a') with _ | ⟨y, ys⟩
        · exact absurd hcf hne
        · rw [hcf] at hx hhd
          simp at hx ⊢
          exact hhd x (by simp [hx])
