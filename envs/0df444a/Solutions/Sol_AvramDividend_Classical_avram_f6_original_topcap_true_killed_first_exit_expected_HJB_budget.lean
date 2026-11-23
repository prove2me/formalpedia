-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_topcap_true_killed_first_exit_expected_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:13:53.609041+00:00
-- url     : https://prove2.me/submissions/2abb2802-ef7f-4417-b59e-3ff72a059806
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_growth_20261123_gaussian_original_killed_exit_budget
import Theorems.Thm_AvramDividend_Classical_avram_growth_20261123_zeroSigma_original_killed_exit_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectation X q b 1).toReal ≤ w 1 := by
  by_cases hSigma0 : X.σ = 0
  · exact AvramDividend.Classical.avram_growth_20261123_zeroSigma_original_killed_exit_budget X hX hBV hν q hq w C hC hTop hw0 hwcont hwneg hwsmooth hwgen hwgrad hSigma0
  · exact AvramDividend.Classical.avram_growth_20261123_gaussian_original_killed_exit_budget X hX hBV hν q hq w C hC hTop hw0 hwcont hwneg hwsmooth hwgen hwgrad hSigma0
