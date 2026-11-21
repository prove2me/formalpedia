-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn16_purejump_HJB_global_exponential_growth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T18:24:31.555156+00:00
-- url     : https://prove2.me/submissions/2789af24-7bde-45cf-aa51-a463aed40502
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_negative_jump_intensity_infinite
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_infinite_activity_topcap_HJB_growth_purejump


open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hCtop : C = ⊤) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by
  have hinfinite : X.ν (Iio (0 : ℝ)) = ⊤ :=
    avram_f6_purejump_ubv_negative_jump_intensity_infinite X hBV hσ
  obtain ⟨θ, K, hθ, hK, hpos⟩ :=
    avram_f6_original_infinite_activity_topcap_HJB_growth_purejump
      X hX hBV hν q hq w C hC hCtop hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hinfinite hσ
  refine ⟨θ, K, hθ, hK, ?_⟩
  intro y
  by_cases hy : 0 ≤ y
  · exact hpos y hy
  · have hyneg : y < 0 := lt_of_not_ge hy
    rw [hw_neg y hyneg]
    exact mul_nonneg hK (le_of_lt (Real.exp_pos _))
