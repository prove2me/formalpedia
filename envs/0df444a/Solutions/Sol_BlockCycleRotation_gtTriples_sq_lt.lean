-- Prove2me | solution 1 for BlockCycleRotation.gtTriples_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:16:42.631995+00:00
-- url     : https://prove2.me/submissions/bc2fdc2f-96c4-439d-9393-fd170a72910a

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
/-- **The key restriction.**  On `gtTriples m d` we have `d·a² < m`, so
`a ≤ √(m/d)`.  This is what makes the error sum converge. -/
theorem solution {m d a a' b' : ℕ} (h : (a, a', b') ∈ gtTriples m d) :
    d * a * a < m:= by
  obtain ⟨⟨⟨-, -, -, hb1, hlt, -⟩, -⟩, hgt⟩ := mem_gtTriples.1 h
  omega
