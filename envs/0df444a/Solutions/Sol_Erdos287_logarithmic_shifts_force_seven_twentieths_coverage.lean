-- Prove2me | solution 1 for Erdos287.logarithmic_shifts_force_seven_twentieths_coverage
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:04:06.774542+00:00
-- url     : https://prove2.me/submissions/7407e5da-07d5-47ee-95f3-c004e3ddacf0

import Mathlib
import Theorems.Thm_Erdos287_logarithmic_shifts_cover_length_bound

open Finset

set_option autoImplicit false

/-- Two ways of grouping the logarithmic shifts give a stronger joint
length bound for the 49 possible distances between 50 forms. -/
theorem solution (N : ℕ) (hN : 3 ≤ N) (hN₄₉ : N ≤ 49) :
    ∃ r ε : ℝ, 0 < r ∧ r < 1 ∧ 0 < ε ∧
      ∀ (J : Finset ℕ) (l u : ℕ → ℝ) (a b : ℝ),
        (∀ i ∈ J, r ≤ u i - l i) →
        (∀ x ∈ Set.Icc a b, ∃ i ∈ J, ∃ z ∈ Set.Icc (l i) (u i - r),
          ∃ d ∈ Finset.Icc 1 N, |x - (z + Real.log d)| ≤ ε) →
        7 * (b - a) ≤ 20 * ∑ i ∈ J, (u i - l i) := by
  let Q := Real.log (49 / 2 : ℝ) + 6 * Real.log (49 / 3 : ℝ)
  have hQ₀ : 0 < Q := by
    have hp₂ : 0 < Real.log (49 / 2 : ℝ) := Real.log_pos (by norm_num)
    have hp₃ : 0 < Real.log (49 / 3 : ℝ) := Real.log_pos (by norm_num)
    dsimp [Q]
    linarith
  have hQ₂₀ : Q < 20 := by
    let c : ℝ := (49 / 2) * (49 / 3) ^ 6
    have hc : 0 < c := by dsimp [c]; positivity
    have hcmp : c < Real.exp 20 := by
      calc
        c < (2718 / 1000 : ℝ) ^ (20 : ℕ) := by norm_num [c]
        _ < (Real.exp 1) ^ (20 : ℕ) := by
          gcongr
          linarith [Real.exp_one_gt_d9]
        _ = Real.exp 20 := by rw [← Real.exp_nat_mul]; norm_num
    have heq : Real.log c = Q := by
      dsimp [c, Q]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    rw [← heq, ← Real.log_exp (20 : ℝ)]
    exact Real.log_lt_log hc hcmp
  let r := (Q + 20) / 40
  let ε := (20 - Q) / 160
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hbudget : Q + 40 * ε ≤ 20 * r := by dsimp [r, ε]; linarith
  have hlog : Real.log (N : ℝ) ≤ Real.log 49 :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by exact_mod_cast hN₄₉)
  have h₂ : Real.log (N : ℝ) - Real.log 2 ≤ Real.log (49 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith
  have h₃ : Real.log (N : ℝ) - Real.log 3 ≤ Real.log (49 / 3 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith
  refine ⟨r, ε, by dsimp [r]; linarith, by dsimp [r]; linarith, hε, ?_⟩
  intro J l u a b hl hcover
  have hcov₂ := Erdos287.logarithmic_shifts_cover_length_bound
    J l u a b r ε N 2 hε.le (by decide) (by omega) hl hcover
  have hcov₃ := Erdos287.logarithmic_shifts_cover_length_bound
    J l u a b r ε N 3 hε.le (by decide) hN hl hcover
  let w (i : ℕ) := u i - l i - r + 2 * ε
  let g₂ (i : ℕ) := 2 * w i + (Real.log (N : ℝ) - Real.log 2)
  let g₃ (i : ℕ) := 3 * w i + (Real.log (N : ℝ) - Real.log 3)
  have hb₂ : b - a ≤ ∑ i ∈ J, g₂ i := by
    simpa only [g₂, w, Nat.cast_ofNat] using hcov₂
  have hb₃ : b - a ≤ ∑ i ∈ J, g₃ i := by
    simpa only [g₃, w, Nat.cast_ofNat] using hcov₃
  calc
    7 * (b - a) = (b - a) + 6 * (b - a) := by ring
    _ ≤ (∑ i ∈ J, g₂ i) + 6 * (∑ i ∈ J, g₃ i) :=
      add_le_add hb₂ (mul_le_mul_of_nonneg_left hb₃ (by norm_num))
    _ = ∑ i ∈ J, (g₂ i + 6 * g₃ i) := by
      have hg₃ : 6 * (∑ i ∈ J, g₃ i) = ∑ i ∈ J, 6 * g₃ i := by
        rw [mul_sum]
      calc
        _ = (∑ i ∈ J, g₂ i) + (∑ i ∈ J, 6 * g₃ i) :=
          congrArg (fun q => (∑ i ∈ J, g₂ i) + q) hg₃
        _ = _ := (sum_add_distrib (s := J) (f := g₂) (g := fun i => 6 * g₃ i)).symm
    _ ≤ ∑ i ∈ J, 20 * (u i - l i) := by
      apply sum_le_sum
      intro i _
      dsimp [g₂, g₃, w, Q] at hbudget ⊢
      linarith only [h₂, h₃, hbudget]
    _ = 20 * ∑ i ∈ J, (u i - l i) := by rw [mul_sum]

