-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_kernel_finite_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:21:34.176815+00:00
-- url     : https://prove2.me/submissions/4e45953b-6ce5-42b6-905c-f44fb285f28c

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_unweighted_kernel_ae_finite
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_antitone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Finite Gaussian Esscher double-tail mass at every strictly positive time. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) < ⊤ := by
  have hae :=
    gaussian_double_tail_unweighted_kernel_ae_finite μ φ hφ hlevy
  have hnonzero : (volume : Measure ℝ) (Ioo (0 : ℝ) t) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by simpa using ht))
  obtain ⟨s, hs, hsfin⟩ :=
    (volume : Measure ℝ).exists_mem_of_measure_ne_zero_of_ae
      hnonzero (ae_restrict_of_ae hae)
  exact lt_of_le_of_lt
    (gaussian_double_tail_kernel_antitone μ φ s t hs.1 (le_of_lt hs.2))
    hsfin
