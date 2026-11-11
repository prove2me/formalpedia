-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_negative_jump_generator_kernel_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:23:19.096561+00:00
-- url     : https://prove2.me/submissions/4f5bc9e8-714e-43a5-95ba-c8fbdd7a9719

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Negative marks cannot reduce the compensated kernel below minus current reward. -/
theorem solution
    (w : ℝ → ℝ) (y z : ℝ) (hz : z < 0)
    (hwyz : 0 ≤ w (y + z)) (hDeriv : 0 ≤ deriv w y) :
    -w y ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by
  unfold SpectrallyNegativeLevy.generatorIntegrand
  by_cases hsmall : z ∈ Ioo (-1 : ℝ) 1
  · have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) z = 1 := by
      simp [Set.indicator_of_mem hsmall]
    rw [hind]
    have hneg : deriv w y * z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hDeriv (le_of_lt hz)
    linarith
  · have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) z = 0 := by
      simp [Set.indicator_of_notMem hsmall]
    rw [hind]
    simp only [mul_zero, sub_zero]
    linarith
