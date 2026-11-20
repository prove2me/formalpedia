-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:48:23.347437+00:00
-- url     : https://prove2.me/submissions/8e43fa46-7e30-4d1d-96da-76ad432677e9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {ι : Type*} (S : Finset ι)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (pre post weight : ι → ℝ)
    (hpost : ∀ i ∈ S, 0 ≤ post i)
    (hmono : ∀ i ∈ S, post i ≤ pre i)
    (hweight : ∀ i ∈ S, 0 ≤ weight i) :
    (∑ i ∈ S, weight i *
      ((pre i - post i) - (V (pre i) - V (post i)))) ≤ 0 := by 
  classical
  apply Finset.sum_nonpos
  intro i hi
  have hsec : pre i - post i ≤ V (pre i) - V (post i) :=
    avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      (post i) (pre i) (hpost i hi) (hmono i hi)
  exact mul_nonpos_of_nonneg_of_nonpos
    (hweight i hi) (sub_nonpos.mpr hsec)
