-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f5_topcap_analytic_HJB_global_exponential_growth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:54:44.246053+00:00
-- url     : https://prove2.me/submissions/5101eade-48fc-4ab5-b4a1-539f6be6dc5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_infinite_activity_HJB_exponential_growth
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y)  := by
  by_cases hInfinite : X.ν (Iio (0 : ℝ)) = ⊤
  · obtain ⟨θ, K, hθ, hK, hBound⟩ :=
      avram_f6_original_topcap_infinite_activity_HJB_exponential_growth
        X hX hBV hν q hq w C hC hTop hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad hInfinite
    refine ⟨θ, K, hθ, hK, ?_⟩
    intro y
    by_cases hy : y < 0
    · rw [hw_neg y hy]
      exact mul_nonneg hK (le_of_lt (Real.exp_pos _))
    · exact hBound y (le_of_not_gt hy)
  · have hFinite : X.ν (Iio (0 : ℝ)) < ⊤ :=
      lt_top_iff_ne_top.mpr hInfinite
    obtain ⟨θ, K, hθ, hK, hBound⟩ :=
      avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
        X hX hBV hFinite q hq w C hC hTop hw0 hw_cont
        hw_neg hw_smooth hw_gen hw_grad
    refine ⟨θ, K, hθ, hK, ?_⟩
    intro y
    by_cases hy : y < 0
    · rw [hw_neg y hy]
      exact mul_nonneg hK (le_of_lt (Real.exp_pos _))
    · exact hBound y (le_of_not_gt hy)
