-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_additive_mean_measure_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:27:55.565836+00:00
-- url     : https://prove2.me/submissions/e1b6a416-4339-4e93-b5ba-899d3c4694a9

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_additive_mean_measure_finite_negative_tails
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual source expected mark measures have strictly negative support,
with separated negative tails finite and exact additive time transport. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ μ : ℝ≥0 → Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ s t : ℝ≥0, μ (s + t) = μ s + μ t) ∧
      (∀ ε : ℝ, 0 < ε → μ 1 (Iic (-ε)) < ⊤) ∧
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B = μ T (B ∩ Iio (0 : ℝ))) := by
  obtain ⟨μ, hRep, hAdd, hFin⟩ :=
    avram_p2_c_borel_original_additive_mean_measure_finite_negative_tails X
  refine ⟨μ, hRep, hAdd, hFin, ?_⟩
  intro T B hB
  rw [hRep T B hB, hRep T (B ∩ Iio (0 : ℝ))
    (hB.inter measurableSet_Iio)]
  apply lintegral_congr
  intro ω
  exact avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
    X ω 0 T B hB
