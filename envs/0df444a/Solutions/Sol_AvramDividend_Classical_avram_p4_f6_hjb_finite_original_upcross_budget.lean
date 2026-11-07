-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_hjb_finite_original_upcross_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:35:30.407196+00:00
-- url     : https://prove2.me/submissions/657f813a-93c4-420b-857c-c44a7b827385
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_original_finite_stopped_supermartingale
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_finite_reward_to_terminal_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Separate the actual physical stopped Dynkin estimate from
the no-positive-jump boundary contact and nonnegative integral comparison. -/
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
      w b * (∫⁻ ω,
        if twoSidedExitUpTimeCorrected X (b - 1) ω <
             twoSidedExitDownTimeCorrected X (-1) ω ∧
           twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then
          ENNReal.ofReal
            (Real.exp (-(q *
              ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω))))
        else 0 ∂P).toReal ≤ w 1 := by
  intro b n hb
  have hboundary :=
    avram_p4_f7_hjb_finite_reward_to_terminal_real
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop b n hb
  have hstopped :=
    avram_p4_f7_hjb_original_finite_stopped_supermartingale
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop b n hb
  exact hboundary.trans hstopped
