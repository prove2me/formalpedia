-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_finitecap_original_C2_interior_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:53:25.256373+00:00
-- url     : https://prove2.me/submissions/2bdda877-2b12-445f-a074-2a3d04adc3d4

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section
/-- The exact original ENNReal-capped interior C² hypothesis implies real-interval differentiability. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ)
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) :
    DifferentiableOn ℝ w (Ioo (0 : ℝ) c) := by
  have hsubset : Ioo (0 : ℝ) c ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c} := by
    intro y hy
    have hy0 : 0 < y := hy.1
    have hyc : y < c := hy.2
    exact ⟨hy0, ENNReal.ofReal_lt_ofReal_iff'.2
      ⟨hyc, lt_trans hy0 hyc⟩⟩
  exact (hwSmooth.mono hsubset).differentiableOn (by norm_num)
