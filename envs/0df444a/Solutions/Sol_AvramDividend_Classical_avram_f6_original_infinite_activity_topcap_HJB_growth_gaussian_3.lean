-- Prove2me | solution 3 for AvramDividend.Classical.avram_f6_original_infinite_activity_topcap_HJB_growth_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:05:53.493079+00:00
-- url     : https://prove2.me/submissions/1329a710-b05e-47cd-ba78-3b4d54841127
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_positive_gaussian_qscale_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_killed_HJB_scale_comparison
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_topcap_global_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_f6_first_exit_scale_cross_inequality_to_domination
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
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
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hInfinite : X.ν (Iio (0 : ℝ)) = ⊤)
    (hCase : 0 < X.σ) :
    ∃ (θ K : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by
  obtain ⟨W, hW, hWone⟩ :=
    avram_p4_f6_positive_gaussian_qscale_exists X hX q hq hCase
  have hσne : X.σ ≠ 0 := ne_of_gt hCase
  have hExit :=
    avram_p4_f6_original_killed_HJB_scale_comparison
      X hX hBV hν hσne q hq w C hC hw0 hwcont
      hwneg hwsmooth hwgen hwgrad hTop W hW hWone
  have hwNonneg : ∀ y : ℝ, 0 ≤ w y :=
    avram_p4_f7_hjb_topcap_global_nonnegative
      w C hw0 hwcont hwneg hwsmooth hwgrad hTop
  obtain ⟨A, hA, hComp⟩ :=
    avram_f6_first_exit_scale_cross_inequality_to_domination
      w W (hwNonneg 1) hWone hExit
  exact avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
    X hBV q hq w hw0 hwcont W hW A hA hComp
