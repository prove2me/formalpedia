-- Prove2me | solution 1 for BlockCycleRotation.gtTriples_bulk_decompose
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:50:43.94657+00:00
-- url     : https://prove2.me/submissions/3598ca4e-2bd8-44d1-8e7b-7911ce8eeff4

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_gtTriples_decompose
import Mathlib

open Finset Real

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
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

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
/-- **The bulk part of the triple sum, decomposed by pairs.** -/
theorem solution {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (d * p.1 + (m - p.2 * b') / p.1):= by
  classical
  have h := gtTriples_decompose (m := m) (d := d) hm
    (fun a a' b' => if d * a * (a + a') ≤ m then d * a + (m - a' * b') / a else 0)
  calc ∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      = ∑ t ∈ gtTriples m d,
          (if d * t.1 * (t.1 + t.2.1) ≤ m then d * t.1 + (m - t.2.1 * t.2.2) / t.1 else 0) :=
        Finset.sum_filter _ _
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (if d * p.1 * (p.1 + p.2) ≤ m then d * p.1 + (m - p.2 * b') / p.1 else 0) := h
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          (if d * p.1 * (p.1 + p.2) ≤ m then
            ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
              (d * p.1 + (m - p.2 * b') / p.1) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with hb
        · rfl
        · simp
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (d * p.1 + (m - p.2 * b') / p.1) := by
        rw [← Finset.sum_filter, Finset.filter_filter]
        refine Finset.sum_congr (Finset.filter_congr fun p hp => ?_) (fun _ _ => rfl)
        obtain ⟨a, a'⟩ := p
        obtain ⟨-, ha1, haa, -⟩ := mem_coprimePairs.1 hp
        have ha : 0 < a := by omega
        constructor
        · rintro ⟨-, h2⟩; exact h2
        · intro h2
          refine ⟨?_, h2⟩
          have hpos : 0 < d * a * a' := Nat.mul_pos (Nat.mul_pos hd ha) (by omega)
          have hlt : d * a * a < d * a * (a + a') := by nlinarith
          exact lt_of_lt_of_le hlt h2
