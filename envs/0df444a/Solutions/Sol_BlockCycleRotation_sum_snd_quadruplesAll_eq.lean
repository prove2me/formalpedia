-- Prove2me | solution 1 for BlockCycleRotation.sum_snd_quadruplesAll_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:10:35.921761+00:00
-- url     : https://prove2.me/submissions/1f6370b7-d1e2-47fb-b929-623ed964a13b

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

/-- The components of a quadruple are bounded by `n`. -/
theorem quadruple_le {n a b a' b' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : 1 ≤ b')
    (h4 : b' < b) (hsum : n = a * b + a' * b') :
    a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n := by
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem mem_quadruplesAll {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruplesAll n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ Nat.gcd a a' = 1 ∧ n = a * b + a' * b' := by
  simp [quadruplesAll, Finset.mem_filter, Finset.mem_product, and_assoc]

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

end BlockCycleRotation

open BlockCycleRotation in
/-- The `b`-elimination for the coprime quadruples. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesAll n, q.2.1
      = ∑ t ∈ coprimeTriples n, (n - t.2.1 * t.2.2) / t.1:= by
  refine Finset.sum_bij'
    (i := fun q _ => (q.1, q.2.2.1, q.2.2.2))
    (j := fun t _ => (t.1, (n - t.2.1 * t.2.2) / t.1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨⟨hab, hbb, ha'b, hb'b⟩, ha1, ha2, hb1, hb2, hgcd, hsum⟩ := mem_quadruplesAll.1 hq
    have hdvd : a ∣ (n - a' * b') := ⟨b, by omega⟩
    have hlt : (a + a') * b' < n := by nlinarith
    show (a, a', b') ∈ coprimeTriples n
    rw [mem_coprimeTriples]
    exact ⟨⟨⟨hab, ha'b, hb'b⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩ := mem_coprimeTriples.1 ht
    have ha : 0 < a := by omega
    have hab : a * ((n - a' * b') / a) = n - a' * b' := Nat.mul_div_cancel' hdvd
    have hle : a' * b' ≤ n := by nlinarith
    have hsum : n = a * ((n - a' * b') / a) + a' * b' := by omega
    have hbb : b' < (n - a' * b') / a := by
      have h1 : a * b' < a * ((n - a' * b') / a) := by rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    show (a, (n - a' * b') / a, a', b') ∈ quadruplesAll n
    rw [mem_quadruplesAll]
    exact ⟨quadruple_le ha1 ha2 hb1 hbb hsum, ha1, ha2, hb1, hbb, hgcd, hsum⟩
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, hb1, hb2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have ha : 0 < a := by omega
    have h : n - a' * b' = a * b := by omega
    show (a, (n - a' * b') / a, a', b') = (a, b, a', b')
    rw [h, Nat.mul_div_cancel_left _ ha]
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, hb1, hb2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have ha : 0 < a := by omega
    have h : n - a' * b' = a * b := by omega
    show b = (n - a' * b') / a
    rw [h, Nat.mul_div_cancel_left _ ha]
