-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_discounted_physical_dividend_cell_gradient_losses_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:41:07.641292+00:00
-- url     : https://prove2.me/submissions/51a8db5e-d154-4f1b-8c87-083e54cf5180

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {ι : Type*} (S : Finset ι)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (pre post weight : ι → ℝ)
    (hpost : ∀ i ∈ S, 0 ≤ post i)
    (hpre : ∀ i ∈ S, post i ≤ pre i)
    (hcap : ∀ i ∈ S, ENNReal.ofReal (pre i) ≤ C)
    (hwgt : ∀ i ∈ S, 0 ≤ weight i) :
    (∑ i ∈ S, weight i *
      ((pre i - post i) - (w (pre i) - w (post i)))) ≤ 0 := by 
  classical
  apply Finset.sum_nonpos
  intro i hi
  have hsec : pre i - post i ≤ w (pre i) - w (post i) :=
    avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      C w hw_cont hw_smooth hw_grad
      (post i) (pre i) (hpost i hi) (hpre i hi) (hcap i hi)
  exact mul_nonpos_of_nonneg_of_nonpos
    (hwgt i hi) (sub_nonpos.mpr hsec)
