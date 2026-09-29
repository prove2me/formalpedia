-- Prove2me | solution 1 for BlockCycleRotation.small_two_mul_gt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:24:52.647477+00:00
-- url     : https://prove2.me/submissions/d680224f-ddb0-47a8-a7fc-f54731dd31d0

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

theorem mem_triples {n a a' b' : ℕ} :
    (a, a', b') ∈ triples n ↔
      (a ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b'
        ∧ (a + a') * b' < n ∧ a ∣ (n - a' * b') := by
  simp [triples, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem mem_coprimeTriples {n a a' b' : ℕ} :
    (a, a', b') ∈ coprimeTriples n ↔
      ((a ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b'
        ∧ (a + a') * b' < n ∧ a ∣ (n - a' * b')) ∧ Nat.gcd a a' = 1 := by
  simp [coprimeTriples, Finset.mem_filter, mem_triples]

theorem mem_gtTriples {m d a a' b' : ℕ} :
    (a, a', b') ∈ gtTriples m d ↔
      (((a ≤ m ∧ a' ≤ m ∧ b' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b'
        ∧ (a + a') * b' < m ∧ a ∣ (m - a' * b')) ∧ Nat.gcd a a' = 1)
        ∧ d * a * a < m - a' * b' := by
  simp [gtTriples, Finset.mem_filter, mem_coprimeTriples]

end BlockCycleRotation

open BlockCycleRotation in
/-- **On the small branch, `2·d·a² > m`.**  This is the paper's observation that
`2a²` is bounded below by `m/d`, which is what makes the small part small. -/
theorem solution {m d a a' b' : ℕ} (h : (a, a', b') ∈ gtTriples m d)
    (hsmall : m < d * a * (a + a')) : m < 2 * (d * a * a):= by
  obtain ⟨⟨⟨-, -, ha2, -, -, -⟩, -⟩, -⟩ := mem_gtTriples.1 h
  nlinarith
