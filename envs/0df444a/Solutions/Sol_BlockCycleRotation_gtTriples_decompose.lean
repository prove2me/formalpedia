-- Prove2me | solution 1 for BlockCycleRotation.gtTriples_decompose
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:18:04.532558+00:00
-- url     : https://prove2.me/submissions/ec5178ae-a597-470b-8c1a-755435da6fda

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

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem mem_gtTriples {m d a a' b' : ℕ} :
    (a, a', b') ∈ gtTriples m d ↔
      (((a ≤ m ∧ a' ≤ m ∧ b' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b'
        ∧ (a + a') * b' < m ∧ a ∣ (m - a' * b')) ∧ Nat.gcd a a' = 1)
        ∧ d * a * a < m - a' * b' := by
  simp [gtTriples, Finset.mem_filter, mem_coprimeTriples]

theorem mem_gtRange {m d a a' b' : ℕ} (hm : 0 < m) (haa : 0 < a + a') (ha' : 0 < a')
    (hda : d * a * a < m) :
    b' ∈ Finset.Ico 1 (gtBound m d a a')
      ↔ (1 ≤ b' ∧ (a + a') * b' < m ∧ a' * b' + d * a * a < m) := by
  rw [Finset.mem_Ico, gtBound, lt_min_iff, Nat.lt_succ_iff, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le haa, Nat.le_div_iff_mul_le ha',
    Nat.mul_comm b' (a + a'), Nat.mul_comm b' a']
  omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **The restricted triple sum, decomposed by pairs.** -/
theorem solution {m d : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ gtTriples m d, f t.1 t.2.1 t.2.2
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter
            (fun b' => p.1 ∣ (m - p.2 * b')), f p.1 p.2 b':= by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun t _ => (⟨(t.1, t.2.1), t.2.2⟩ : (_ : ℕ × ℕ) × ℕ))
    (j := fun p _ => (p.1.1, p.1.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩, hgt⟩ := mem_gtTriples.1 ht
    have haa : 0 < a + a' := by omega
    have hle : a' * b' ≤ m := by nlinarith
    have hda : d * a * a < m := by omega
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨⟨mem_coprimePairs.2 ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩, hda⟩,
      (mem_gtRange hm haa (by omega) hda).2 ⟨hb1, hlt, by omega⟩, hdvd⟩
  · rintro ⟨⟨a, a'⟩, b'⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨⟨hpair, hda⟩, hb, hdvd⟩ := hp
    obtain ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair
    have haa : 0 < a + a' := by omega
    obtain ⟨hb1, hlt, hgt⟩ := (mem_gtRange hm haa (by omega) hda).1 hb
    have hb'n : b' ≤ m := by nlinarith
    show (a, a', b') ∈ gtTriples m d
    rw [mem_gtTriples]
    have hle : a' * b' ≤ m := by nlinarith
    exact ⟨⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩, by omega⟩
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨⟨a, a'⟩, b'⟩ _
    rfl
  · rintro ⟨a, a', b'⟩ _
    rfl
