-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB293_ae_gaussian_kernel_cell_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:14:01.441474+00:00
-- url     : https://prove2.me/submissions/c90a1ef9-6f06-4fcb-b6b0-7043b70edceb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

/-- Almost-everywhere Gaussian elapsed-time envelope gives a finite translated-cell integral bound. -/
theorem solution (s δ K : ℝ) (hδ : 0 ≤ δ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume s (s + δ))
    (hg : IntervalIntegrable
      (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume s (s + δ))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Icc s (s + δ))),
      f t ≤ K * (t - s) ^ (-(1 / 2 : ℝ))) :
    (∫ t in s..(s + δ), f t) ≤ 2 * K * Real.sqrt δ := by
  have hKg : IntervalIntegrable
      (fun t : ℝ => K * (t - s) ^ (-(1 / 2 : ℝ)))
      volume s (s + δ) := hg.const_mul K
  have hle := intervalIntegral.integral_mono_ae_restrict
    (by linarith : s ≤ s + δ) hf hKg hbound
  calc
    (∫ t in s..(s + δ), f t) ≤
        (∫ t in s..(s + δ), K * (t - s) ^ (-(1 / 2 : ℝ))) := hle
    _ = K * (∫ t in s..(s + δ), (t - s) ^ (-(1 / 2 : ℝ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = K * (2 * Real.sqrt δ) := by
      rw [avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral]
    _ = 2 * K * Real.sqrt δ := by ring
