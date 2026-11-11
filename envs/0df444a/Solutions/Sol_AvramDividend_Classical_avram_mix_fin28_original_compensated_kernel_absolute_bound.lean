-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin28_original_compensated_kernel_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:10:20.793399+00:00
-- url     : https://prove2.me/submissions/a8d90444-90b6-41ad-a714-12e15ea5f524

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin27_original_negative_mark_reward_increment_bounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t < 0, w t = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C})
    (hw_grad : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t < C → 1 ≤ deriv w t)
    (y z : ℝ) (hy : 0 < y)
    (hyC : ENNReal.ofReal y < C) (hz : z < 0) :
    |SpectrallyNegativeLevy.generatorIntegrand w y z| ≤
      w y + |deriv w y| := by
  have habs :=
    avram_mix_fin27_original_negative_mark_reward_increment_bounded
      C hC w hw0 hw_cont hw_neg hw_smooth hw_grad
      y z hy hyC hz
  unfold SpectrallyNegativeLevy.generatorIntegrand
  by_cases hsmall : z ∈ Ioo (-1 : ℝ) 1
  · have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) z = 1 := by
      simp [Set.indicator_of_mem hsmall]
    rw [hind]
    simp only [mul_one]
    have hzabs : |z| ≤ (1 : ℝ) := by
      apply abs_le.mpr
      exact ⟨le_of_lt hsmall.1, le_of_lt hsmall.2⟩
    have hprod : |deriv w y * z| ≤ |deriv w y| := by
      rw [abs_mul]
      simpa using
        (mul_le_mul_of_nonneg_left hzabs (abs_nonneg (deriv w y)))
    calc
      |w (y + z) - w y - deriv w y * z| ≤
          |w (y + z) - w y| + |deriv w y * z| := by
        simpa using (abs_sub_le (w (y + z) - w y) 0 (deriv w y * z))
      _ ≤ w y + |deriv w y| := add_le_add habs hprod
  · have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) z = 0 := by
      simp [Set.indicator_of_notMem hsmall]
    rw [hind]
    simp only [mul_zero, sub_zero]
    exact habs.trans (le_add_of_nonneg_right (abs_nonneg _))
