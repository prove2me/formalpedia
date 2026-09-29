-- Prove2me | solution 1 for BlockCycleRotation.bulk_empty_of_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:31:01.157666+00:00
-- url     : https://prove2.me/submissions/bf5cedca-c6cb-4cbd-ab4a-4661a39c8ea5

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
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

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

end BlockCycleRotation

open BlockCycleRotation in
/-- **The bulk set is empty when `m` is small relative to `d`.** -/
theorem solution {m d : ℕ} (h : m < 6 * d) :
    (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m) = ∅:= by
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨a, a'⟩ hp
  obtain ⟨-, ha1, ha2, -⟩ := mem_coprimePairs.1 hp
  have ha2' : 2 ≤ a := by omega
  have haa : 3 ≤ a + a' := by omega
  intro hcon
  have hcon' : d * a * (a + a') ≤ m := hcon
  have hge : 6 * d ≤ d * a * (a + a') := by
    calc 6 * d = d * 2 * 3 := by ring
      _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul_left d ha2') haa
  omega
