-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_test_intrinsic_jump_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:39:49.429214+00:00
-- url     : https://prove2.me/submissions/6f72f274-4580-4383-916c-106890cc578a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_test_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_uniform_grid_compact_negative_levy_expectation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Identify the original finite-jump intrinsic sum's expectation by uniqueness
of the source-grid expectation limit and the independently proved levy rate. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f ((X.X u ω - X.X 0 ω) -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F, f ((X.X u ω - X.X 0 ω) -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u)) ∧
      (∫ ω, J ω ∂P) =
        (T : ℝ) * (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))) := by
  obtain ⟨J, hJI, hJsum, _, hJexp⟩ :=
    avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
      P X T hT f hf hc hneg
  have hInt : ∀ t : ℝ≥0, Integrable (fun ω => f (X.X t ω)) P := by
    intro t
    exact avram_p2_j_ui_original_compact_test_integrable X t f hf hc
  have hGrid :=
    avram_p2_d_future_original_uniform_grid_compact_negative_levy_expectation
      P X f hf a ε hε hflower hfupper hInt T hT
  have heq := tendsto_nhds_unique hJexp hGrid
  exact ⟨J, hJI, hJsum, heq⟩
