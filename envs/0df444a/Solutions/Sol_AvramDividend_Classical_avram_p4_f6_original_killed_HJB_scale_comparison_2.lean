-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f6_original_killed_HJB_scale_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:34:39.92627+00:00
-- url     : https://prove2.me/submissions/c3f9586f-2b3f-4854-ae4b-1191b2f1b378
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_qscale_killed_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_HJB_killed_upcross_expectation_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWone : 0 < W 1) :
    ∀ b : ℝ, 1 ≤ b → w b * W 1 ≤ w 1 * W b := by
  classical
  intro b hb
  have hScale :=
    avram_p4_f6_original_qscale_killed_exit_factorisation
      X hX q hq W hW hWone b hb
  have hBudget :=
    avram_p4_f6_original_HJB_killed_upcross_expectation_bound
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop b hb
  have hWb : 0 ≤ W b :=
    (le_of_lt hWone).trans ((scaleFunction_monotone X q W hW) hb)
  calc
    w b * W 1 =
        (w b * (twoSidedExitExpectationCorrected X q b 1).toReal) * W b := by
      rw [hScale]
      ring
    _ ≤ w 1 * W b := mul_le_mul_of_nonneg_right hBudget hWb
