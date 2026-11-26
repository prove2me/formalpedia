-- Prove2me | solution 1 for Erdos287.many_unit_gaps_and_eight_runs_from_endpoint_ratio
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:21:23.98654+00:00
-- url     : https://prove2.me/submissions/253b8005-21b6-47a8-904e-aac6d0656db0

import Mathlib
import Theorems.Thm_Erdos287_count_and_unit_gaps_lower_bound_from_first_denominator
import Theorems.Thm_Erdos287_consecutive_runs_from_denominator_density

open Finset

set_option autoImplicit false

/-- The narrow endpoint ratio forces explicit counts of unit gaps and
length-eight runs in a putative representation with no gap at least three. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hfirst : 3000 ≤ f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hratio : 250 * f (k - 1) ≤ 739 * f 0)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    let D := (Finset.range k).image f
    let R := (Finset.Icc (f 0) (f (k - 1) + 1 - 8)).filter
      (fun x => ∀ i ∈ Finset.range 8, x + i ∈ D)
    let U := (Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)
    f (k - 1) < 2 * U.card ∧ f (k - 1) < 100 * R.card := by
  classical
  dsimp only
  let m := f 0
  let M := f (k - 1)
  let D := (range k).image f
  let R := (Icc m (M + 1 - 8)).filter (fun x => ∀ i ∈ range 8, x + i ∈ D)
  let U := (range (k - 1)).filter (fun i => f (i + 1) - f i = 1)
  change M < 2 * U.card ∧ M < 100 * R.card
  have hm : 3000 ≤ m := hfirst
  have hlast : k - 1 < k := by omega
  have hmin : 1 < f 0 := by omega
  have hmM : m ≤ M := (hmono 0 (k - 1) (by omega) hlast).le
  have hD : D ⊆ Icc m M := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hi' := mem_range.mp hi
    apply mem_Icc.mpr
    constructor
    · by_cases hzero : i = 0
      · simp [hzero, m]
      · exact (hmono 0 i (by omega) hi').le
    · by_cases heq : i = k - 1
      · simp [heq, M]
      · exact (hmono i (k - 1) (by omega) hlast).le
  have hinj : Set.InjOn f (↑(range k) : Set ℕ) := by
    intro i hi j hj h
    have hi' := mem_range.mp (show i ∈ range k from hi)
    have hj' := mem_range.mp (show j ∈ range k from hj)
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ((hmono i j hij hj').ne h).elim
    · exact hij
    · exact ((hmono j i hij hi').ne h.symm).elim
  have hDcard : D.card = k := by
    change ((range k).image f).card = k
    rw [card_image_of_injOn hinj, card_range]
  have hDcap : D.card ≤ M + 1 - m := (card_le_card hD).trans_eq (Nat.card_Icc _ _)
  have hkcap : k ≤ M + 1 - m := hDcard ▸ hDcap
  have hmM' : m ≤ M + 1 := by omega
  have hratioR : (250 : ℝ) * M ≤ 739 * m := by exact_mod_cast hratio
  have hmR : (3000 : ℝ) ≤ m := by exact_mod_cast hm
  have hE : (2718 / 1000 : ℝ) ≤ Real.exp 1 :=
    le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have hEterm := mul_le_mul_of_nonneg_right hE (show 0 ≤ (m : ℝ) - 1 by linarith)
  have ⟨hcount, hunit⟩ := Erdos287.count_and_unit_gaps_lower_bound_from_first_denominator
    k hk f hmin hmono hsum
  have hcount' : (Real.exp 1 - 1) * ((m : ℝ) - 1) ≤ (k : ℝ) := hcount
  have hunit' : (2 * Real.exp 1 - 1) * m - M - 2 * Real.exp 1 ≤ (U.card : ℝ) := hunit hgap
  have hcountLow : (1718 / 1000 : ℝ) * ((m : ℝ) - 1) ≤ k := by
    nlinarith only [hEterm, hcount']
  have hunitLow : (4436 / 1000 : ℝ) * m - M - 5436 / 1000 ≤ (U.card : ℝ) := by
    nlinarith only [hEterm, hunit']
  have hrun := Erdos287.consecutive_runs_from_denominator_density m M 8 (by decide)
    (by omega) D hD
  change M + 2 ≤ m + 8 + 8 * (M + 1 - m - D.card) + R.card at hrun
  have hrunR : ((M + 2 : ℕ) : ℝ) ≤ ((m + 8 + 8 * (M + 1 - m - D.card) + R.card : ℕ) : ℝ) := by
    exact_mod_cast hrun
  push_cast [Nat.cast_sub hkcap, Nat.cast_sub hmM', hDcard] at hrunR
  have hunitGoal : (M : ℝ) < 2 * U.card := by
    linarith only [hunitLow, hmR, hratioR]
  have hrunGoal : (M : ℝ) < 100 * R.card := by
    linarith only [hrunR, hcountLow, hmR, hratioR]
  exact ⟨by exact_mod_cast hunitGoal, by exact_mod_cast hrunGoal⟩

