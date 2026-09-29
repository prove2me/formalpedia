-- Prove2me | solution 1 for BlockCycleRotation.divisor_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:51:05.69575+00:00
-- url     : https://prove2.me/submissions/cf20265a-6166-4ca5-8c1a-b3ec203a6871

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_middle_layer
import Theorems.Thm_BlockCycleRotation_small_part_le
import Theorems.Thm_BlockCycleRotation_bulk_pair_estimate
import Theorems.Thm_BlockCycleRotation_gtTriples_bulk_decompose
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

/-- **The bulk / small split of the triple sum.** -/
theorem gtTriples_bulk_small (m d : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ gtTriples m d, f t.1 t.2.1 t.2.2
      = (∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          f t.1 t.2.1 t.2.2)
        + ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
            f t.1 t.2.1 t.2.2 :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end BlockCycleRotation

open BlockCycleRotation in
/-- **The estimate at a single divisor.**

The triple sum at `d` differs from the `G₁` summand at `d` by at most twice the
middle-layer bound plus the small part. -/
theorem solution {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    |((∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ)
        - ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
            ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
      ≤ 2 * (((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m)))
        + (((Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) : ℕ) : ℝ):= by
  classical
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : (0 : ℝ) ≤ Real.log m := Real.log_nonneg hmR
  set Sb := (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m) with hSb
  -- split the triple sum
  have hsplit : (∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1))
      = (∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          (d * t.1 + (m - t.2.1 * t.2.2) / t.1))
        + ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
            (d * t.1 + (m - t.2.1 * t.2.2) / t.1) :=
    gtTriples_bulk_small m d (fun a a' b' => d * a + (m - a' * b') / a)
  have hbd := gtTriples_bulk_decompose hm hd
  -- the bulk part, pair by pair
  have hpair : ∀ p ∈ Sb,
      |((∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (d * p.1 + (m - p.2 * b') / p.1) : ℕ) : ℝ)
          - ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
        ≤ 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m) := by
    intro p hp
    obtain ⟨a, a'⟩ := p
    rw [hSb, Finset.mem_filter] at hp
    obtain ⟨hpc, hpb⟩ := hp
    obtain ⟨-, ha1, haa, hgcd⟩ := mem_coprimePairs.1 hpc
    exact bulk_pair_estimate hm hd ha1 haa hgcd hpb
  have hbulkest :
      |(∑ p ∈ Sb, ((∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter
              (fun b' => p.1 ∣ (m - p.2 * b')), (d * p.1 + (m - p.2 * b') / p.1) : ℕ) : ℝ))
          - ∑ p ∈ Sb, ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
        ≤ ∑ p ∈ Sb, 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpair)
  -- the pair-error sum is at most twice the middle layer
  have hmid : ∑ p ∈ Sb, 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m)
      ≤ 2 * (((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m))) := by
    have hsub : Sb ⊆ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m) := by
      intro p hp
      rw [hSb, Finset.mem_filter] at hp
      obtain ⟨hpc, hpb⟩ := hp
      refine Finset.mem_filter.2 ⟨hpc, ?_⟩
      obtain ⟨a, a'⟩ := p
      obtain ⟨-, ha1, haa, -⟩ := mem_coprimePairs.1 hpc
      have ha : 0 < a := by omega
      have hpos : 0 < d * a * a' := Nat.mul_pos (Nat.mul_pos hd ha) (by omega)
      have hlt : d * a * a < d * a * (a + a') := by nlinarith
      exact lt_of_lt_of_le hlt hpb
    have hstep : ∑ p ∈ Sb, 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ))
            * (1 + Real.log m)
        ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
            2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    refine hstep.trans ?_
    rw [show ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m)
        = 2 * ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
            ((((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m)) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring]
    exact mul_le_mul_of_nonneg_left (middle_layer (m := m) (d := d) hm hd) (by norm_num)
  -- the small part
  have hsmall := small_part_le hm hd
  have hsmallR : ((∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ)
      ≤ (((Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) : ℕ) : ℝ) := by
    exact_mod_cast hsmall
  have hsmallnn : (0 : ℝ) ≤ ((∑ t ∈ (gtTriples m d).filter
      (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)), (d * t.1 + (m - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ) :=
    by positivity
  -- assemble
  have key : ∀ X Y M b1 b2 : ℝ, |X - M| ≤ b1 → 0 ≤ Y → Y ≤ b2 → |X + Y - M| ≤ b1 + b2 := by
    intro X Y M b1 b2 h1 h2 h3
    have htri := abs_add_le (X - M) Y
    rw [abs_of_nonneg h2] at htri
    have heq : X + Y - M = (X - M) + Y := by ring
    rw [heq]
    linarith
  rw [hsplit, hbd, Nat.cast_add, Nat.cast_sum]
  exact key _ _ _ _ _ (hbulkest.trans hmid) hsmallnn hsmallR
