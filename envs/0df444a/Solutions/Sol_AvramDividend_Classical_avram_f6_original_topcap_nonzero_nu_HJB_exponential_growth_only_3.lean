-- Prove2me | solution 3 for AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exponential_growth_only
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:09:27.902894+00:00
-- url     : https://prove2.me/submissions/12cb78a1-cb6f-445c-8453-1c3904e66983
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_infinite_activity_HJB_exponential_growth
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
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
    ∃ (θ K : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by
  classical
  by_cases hFinite : X.ν (Iio (0 : ℝ)) < ⊤
  · exact avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
      X hX hBV hFinite q hq w C hC hTop hw0 hwcont hwneg
      hwsmooth hwgen hwgrad
  · have hInfinite : X.ν (Iio (0 : ℝ)) = ⊤ :=
      top_unique (not_lt.mp hFinite)
    exact avram_f6_original_topcap_infinite_activity_HJB_exponential_growth
      X hX hBV hν q hq w C hC hTop hw0 hwcont hwneg
      hwsmooth hwgen hwgrad hInfinite
