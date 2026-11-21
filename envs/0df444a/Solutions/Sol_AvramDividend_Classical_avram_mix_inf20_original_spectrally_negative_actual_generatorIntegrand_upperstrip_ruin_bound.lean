-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_spectrally_negative_actual_generatorIntegrand_upperstrip_ruin_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:42:00.846414+00:00
-- url     : https://prove2.me/submissions/c47d66fb-df77-4e2a-8008-6e6a80a87600

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    SpectrallyNegativeLevy.generatorIntegrand V y z ≤ max 0 (-(y + z))  := by
  dsimp only
  have h :=
    avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
      C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hz
  have hGen :
      SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z =
        (if y + z ≤ C.toReal then w (y + z) else
          w C.toReal + (y + z - C.toReal)) -
        (if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal)) -
        deriv (fun t => if t ≤ C.toReal then w t else
          w C.toReal + (t - C.toReal)) y *
          (if -1 < z then z else 0) := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    by_cases hsmall : -1 < z
    · have hz1 : z < 1 := lt_trans hz (by norm_num)
      simp [Set.indicator, Set.mem_Ioo, hsmall, hz1]
    · simp [Set.indicator, Set.mem_Ioo, hsmall]
  rw [hGen]
  exact h
