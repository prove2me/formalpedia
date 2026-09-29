-- Prove2me | solution 1 for BlockCycleRotation.coprimeTriples_decompose
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:12:38.131493+00:00
-- url     : https://prove2.me/submissions/39b25b69-9f6d-4d4c-92b8-39ad7b0ac441

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

theorem mem_bRange {m a a' b' : ℕ} (hm : 0 < m) (ha : 0 < a + a') :
    b' ∈ Finset.Ico 1 (bBound m a a') ↔ 1 ≤ b' ∧ (a + a') * b' < m := by
  rw [Finset.mem_Ico, bBound, Nat.lt_succ_iff, Nat.le_div_iff_mul_le ha,
    Nat.mul_comm b' (a + a')]
  omega

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

end BlockCycleRotation

open BlockCycleRotation in
/-- **The triple sum, decomposed by pairs.** -/
theorem solution {m : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ coprimeTriples m, f t.1 t.2.1 t.2.2
      = ∑ p ∈ coprimePairs m, ∑ b' ∈ (Finset.Ico 1 (bBound m p.1 p.2)).filter
          (fun b' => p.1 ∣ (m - p.2 * b')), f p.1 p.2 b':= by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun t _ => (⟨(t.1, t.2.1), t.2.2⟩ : (_ : ℕ × ℕ) × ℕ))
    (j := fun p _ => (p.1.1, p.1.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩ := mem_coprimeTriples.1 ht
    have ha : 0 < a + a' := by omega
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨mem_coprimePairs.2 ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩,
      (mem_bRange hm ha).2 ⟨hb1, hlt⟩, hdvd⟩
  · rintro ⟨⟨a, a'⟩, b'⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨hpair, hb, hdvd⟩ := hp
    obtain ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair
    have ha : 0 < a + a' := by omega
    obtain ⟨hb1, hlt⟩ := (mem_bRange hm ha).1 hb
    have hb'n : b' ≤ m := by nlinarith
    show (a, a', b') ∈ coprimeTriples m
    rw [mem_coprimeTriples]
    exact ⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨⟨a, a'⟩, b'⟩ _
    rfl
  · rintro ⟨a, a', b'⟩ _
    rfl
