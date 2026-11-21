-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f7_hjb_original_finite_stopped_supermartingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:30:07.753306+00:00
-- url     : https://prove2.me/submissions/640b48cc-516f-4061-9955-0a4f685d2a74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_stopped_dynkin_real_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_topcap_global_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_nonnegative_integrable_lintegral_toReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
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
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) ∂P).toReal ≤ w 1 := by
  classical
  intro b n hb
  let τ : Ω → ℝ≥0∞ := fun ω =>
    min (twoSidedExitUpTimeCorrected X (b - 1) ω)
      (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
  let F : Ω → ℝ := fun ω =>
    Real.exp (-(q * ENNReal.toReal (τ ω))) *
      w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)
  have hBudget :=
    avram_p4_f8_original_stopped_dynkin_real_budget
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop b n hb
  have hPos : ∀ ω, 0 ≤ F ω := by
    intro ω
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (avram_p4_f7_hjb_topcap_global_nonnegative
        w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop _)
  have hEq := avram_p4_f8_nonnegative_integrable_lintegral_toReal
    P F hBudget.1 hPos
  exact hEq.trans_le hBudget.2
