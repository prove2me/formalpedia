-- Prove2me | solution 1 for CountingLLL.RandomRAM.expected_offspring_reduction
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:11:45.724573+00:00
-- url     : https://prove2.me/submissions/aff5dc20-a7ee-45f3-92e5-3674d71360bf

import Theorems.Thm_CountingLLL_RandomRAM_offspring_beta_bound
set_option autoImplicit false
open scoped BigOperators

/-- The source offspring estimate from tree size and per-slot reciprocal-call bounds. -/
theorem solution {ι : Type} [Fintype ι] (p p0 D z : ℝ) (active children : ι → ℝ)
    (hp : 0 ≤ p) (hp0 : 0 ≤ p0) (hp0p : p0 ≤ p) (hD : 1 ≤ D)
    (hcondition : 4 * Real.exp 1 * p * (D+1)^2 ≤ 1)
    (htree : z ≤ p0 / (1-p*D^2))
    (hslots : (∑ i, active i) ≤ (D+1)^2 * z)
    (hchild : ∀ i, children i ≤ active i / (1-p)) :
    (∑ i, children i) ≤ p * (D+1)^2 / ((1-p)*(1-p*D^2)) ∧
    (∑ i, children i) < 1/8 := by
  have hcoef : (10 : ℝ) ≤ 4 * Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hA0 : 0 ≤ p * (D+1)^2 := mul_nonneg hp (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hcoef hA0
  have hA : p * (D+1)^2 ≤ 1/10 := by nlinarith
  have hD2 : (4 : ℝ) ≤ (D+1)^2 := by nlinarith
  have hp4 := mul_le_mul_of_nonneg_left hD2 hp
  have hp40 : p ≤ 1/40 := by nlinarith
  have hDle : D^2 ≤ (D+1)^2 := by nlinarith
  have hpD := mul_le_mul_of_nonneg_left hDle hp
  have hB : p*D^2 ≤ 1/10 := by linarith
  have hd1 : 0 < 1-p := by linarith
  have hd2 : 0 < 1-p*D^2 := by linarith
  have htree' : z ≤ p / (1-p*D^2) := htree.trans (div_le_div_of_nonneg_right hp0p hd2.le)
  have hsum : (∑ i, children i) ≤ (∑ i, active i) / (1-p) := by
    calc
      _ ≤ ∑ i, active i / (1-p) := Finset.sum_le_sum (fun i _ => hchild i)
      _ = _ := by rw [Finset.sum_div]
  have hresult : (∑ i, children i) ≤ p * (D+1)^2 / ((1-p)*(1-p*D^2)) := by
    calc
      _ ≤ (∑ i, active i) / (1-p) := hsum
      _ ≤ ((D+1)^2 * z) / (1-p) := div_le_div_of_nonneg_right hslots hd1.le
      _ ≤ ((D+1)^2 * (p / (1-p*D^2))) / (1-p) := by gcongr
      _ = _ := by field_simp
  exact ⟨hresult, hresult.trans_lt (CountingLLL.RandomRAM.offspring_beta_bound p D hp hD hcondition).2.2⟩
