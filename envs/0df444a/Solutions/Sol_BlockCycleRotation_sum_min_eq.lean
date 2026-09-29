-- Prove2me | solution 1 for BlockCycleRotation.sum_min_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:54:15.879787+00:00
-- url     : https://prove2.me/submissions/68ba98a9-71ad-4fb5-9a0a-a4c9ec7c33ef

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
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

theorem mem_allShifts {n k : ℕ} : k ∈ allShifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n := by
  simp [allShifts]

theorem allShifts_eq_filter {n : ℕ} (hn : 0 < n) :
    allShifts n = (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n) := by
  ext k
  rw [mem_allShifts, Finset.mem_filter, Finset.mem_Ico]
  omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **The double count.** -/
theorem solution {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    (∑ k ∈ Finset.Ico 1 n, f (min k (n - k))) + (if 2 ∣ n then f (n / 2) else 0)
      = 2 * ∑ j ∈ allShifts n, f j:= by
  classical
  rw [allShifts_eq_filter hn]
  have hsplit : ∑ k ∈ Finset.Ico 1 n, f (min k (n - k))
      = (∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f (min k (n - k)))
        + ∑ k ∈ (Finset.Ico 1 n).filter (fun k => ¬ (2 * k ≤ n)), f (min k (n - k)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hAval : ∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f (min k (n - k))
      = ∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_filter, Finset.mem_Ico] at hk
    congr 1
    omega
  have hBval : ∑ k ∈ (Finset.Ico 1 n).filter (fun k => ¬ (2 * k ≤ n)), f (min k (n - k))
      = ∑ j ∈ (Finset.Ico 1 n).filter (fun k => 2 * k < n), f j := by
    refine Finset.sum_bij' (i := fun k _ => n - k) (j := fun k _ => n - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      congr 1
      omega
  have hAA' : ∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f k
      = (∑ j ∈ (Finset.Ico 1 n).filter (fun k => 2 * k < n), f j)
        + (if 2 ∣ n then f (n / 2) else 0) := by
    have hs := (Finset.sum_filter_add_sum_filter_not
      ((Finset.Ico 1 n).filter (fun k => 2 * k ≤ n)) (fun k => 2 * k < n) f).symm
    rw [hs, Finset.filter_filter, Finset.filter_filter]
    congr 1
    · exact Finset.sum_congr (Finset.filter_congr fun k hk => by
        rw [Finset.mem_Ico] at hk; omega) (fun _ _ => rfl)
    · by_cases hev : 2 ∣ n
      · have he : (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n ∧ ¬ (2 * k < n)) = {n / 2} := by
          ext k
          rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
          omega
        rw [he, Finset.sum_singleton, if_pos hev]
      · have he : (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n ∧ ¬ (2 * k < n)) = ∅ := by
          ext k
          rw [Finset.mem_filter, Finset.mem_Ico]
          simp only [Finset.notMem_empty, iff_false]
          omega
        rw [he, Finset.sum_empty, if_neg hev]
  rw [hsplit, hAval, hBval, hAA']
  ring
