-- Prove2me | solution 1 for CountingLLL.RandomRAM.marginal_variance_budget
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:22:02.04623+00:00
-- url     : https://prove2.me/submissions/0a17b163-4cd3-41b1-b38a-e8a7c73eaf5a

import Mathlib
set_option autoImplicit false
open scoped BigOperators

/-- Arithmetic of the relative-variance budget in #442, §5.3. -/
theorem marginal_variance_budget {ι : Type} [Fintype ι]
    (r v : ι → ℝ) (p D L ε : ℝ)
    (hp : 0 ≤ p) (hD : 1 ≤ D) (hL : 0 < L) (he : 0 < ε)
    (hcondition : 4 * Real.exp 1 * p * (D + 1) ^ 2 ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i ≤ (6 / 5) * p)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ 3 * p / L)
    (hLbound : 8 * (Fintype.card ι : ℝ) ≤ L * (D + 1) ^ 2 * ε ^ 2) :
    (∑ i, v i / (1 - r i) ^ 2) ≤ ε ^ 2 / 20 := by
  have hcoef : (10 : ℝ) ≤ 4 * Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hnonneg : 0 ≤ p * (D + 1) ^ 2 := mul_nonneg hp (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hcoef hnonneg
  have hlll : p * (D + 1) ^ 2 ≤ 1 / 10 := by nlinarith
  have hD2 : (4 : ℝ) ≤ (D + 1) ^ 2 := by nlinarith
  have hp4 := mul_le_mul_of_nonneg_left hD2 hp
  have hp_bound : p ≤ 1 / 40 := by nlinarith
  have hr_bound : ∀ i, r i ≤ 3 / 100 := by
    intro i
    have := hr i
    nlinarith
  have hq : 0 ≤ p / L := div_nonneg hp hL.le
  have hfactor : ∀ i, v i / (1 - r i) ^ 2 ≤ 4 * p / L := by
    intro i
    have hd : (3 / 4 : ℝ) ≤ (1 - r i) ^ 2 := by
      have := hr_bound i
      nlinarith [sq_nonneg (r i)]
    have hdpos : 0 < (1 - r i) ^ 2 := by linarith
    apply (div_le_iff₀ hdpos).2
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 * (p / L) by positivity)
    have hv' : v i ≤ 3 * (p / L) := by convert hv i using 1 <;> ring
    have ht : 4 * p / L = 4 * (p / L) := by ring
    rw [ht]
    nlinarith
  have hsum : (∑ i, v i / (1 - r i) ^ 2) ≤ (Fintype.card ι : ℝ) * (4 * p / L) := by
    calc
      _ ≤ ∑ _i : ι, 4 * p / L := Finset.sum_le_sum (fun i _ => hfactor i)
      _ = _ := by simp
  have hbudget : (Fintype.card ι : ℝ) * (4 * p / L) ≤ ε ^ 2 / 20 := by
    have hm := mul_le_mul_of_nonneg_left hLbound hp
    have hll := mul_le_mul_of_nonneg_right hlll (mul_nonneg hL.le (sq_nonneg ε))
    have hraw : (Fintype.card ι : ℝ) * (4 * p) ≤ (ε ^ 2 / 20) * L := by
      nlinarith [hm, hll]
    have hd := (div_le_iff₀ hL).2 hraw
    calc
      _ = ((Fintype.card ι : ℝ) * (4 * p)) / L := by ring
      _ ≤ _ := hd
  exact hsum.trans hbudget

theorem solution {ι : Type} [Fintype ι]
    (r v : ι → ℝ) (p D L ε : ℝ)
    (hp : 0 ≤ p) (hD : 1 ≤ D) (hL : 0 < L) (he : 0 < ε)
    (hcondition : 4 * Real.exp 1 * p * (D + 1) ^ 2 ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i ≤ (6 / 5) * p)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ 3 * p / L)
    (hLbound : 8 * (Fintype.card ι : ℝ) ≤ L * (D + 1) ^ 2 * ε ^ 2) :
    (∑ i, v i / (1 - r i) ^ 2) ≤ ε ^ 2 / 20 :=
  marginal_variance_budget r v p D L ε hp hD hL he hcondition hr0 hr hv0 hv hLbound
