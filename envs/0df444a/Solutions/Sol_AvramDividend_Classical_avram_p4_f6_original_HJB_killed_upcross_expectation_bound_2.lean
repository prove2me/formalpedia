-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f6_original_HJB_killed_upcross_expectation_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:32:17.247553+00:00
-- url     : https://prove2.me/submissions/d4a4437c-1937-4b5d-b34f-c7c09e63935c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_corrected_killed_discount_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_topcap_global_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_clock_budget_to_full
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_original_upcross_budget
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
    ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectationCorrected X q b 1).toReal ≤ w 1 := by
  classical
  intro b hb
  have hMeas :=
    avram_p4_f6_hjb_corrected_killed_discount_measurable X q (-1) (b - 1)
  have hNonneg := avram_p4_f7_hjb_topcap_global_nonnegative
    w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop
  have hFinite : ∀ n : ℕ,
      w b * (∫⁻ ω,
        if twoSidedExitUpTimeCorrected X (b - 1) ω <
             twoSidedExitDownTimeCorrected X (-1) ω ∧
           twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTimeCorrected X (b - 1) ω).toReal)))
        else 0 ∂P).toReal ≤ w 1 := by
    intro n
    exact avram_p4_f6_hjb_finite_original_upcross_budget
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop b n hb
  exact avram_p4_f6_hjb_finite_clock_budget_to_full P
    (fun ω => twoSidedExitUpTimeCorrected X (b - 1) ω)
    (fun ω => twoSidedExitDownTimeCorrected X (-1) ω)
    (fun ω => ENNReal.ofReal
      (Real.exp (-(q * (twoSidedExitUpTimeCorrected X (b - 1) ω).toReal))))
    hMeas.1 hMeas.2.1 hMeas.2.2 (w b) (w 1)
    (hNonneg b) (hNonneg 1) hFinite
