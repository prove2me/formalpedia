-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_additive_mean_measure_finite_negative_tails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:01:38.42727+00:00
-- url     : https://prove2.me/submissions/dca6cbad-4af1-4bda-a64b-d99b66fb21d6

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_mark_measure_time_additive
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_band_finite_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-mark expected measures are time-additive and locally finite away
from zero, independently of their identification with the Lévy ν. -/
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
      (∀ ε : ℝ, 0 < ε → μ 1 (Iic (-ε)) < ⊤) := by
  obtain ⟨μ, hRep, hAdd⟩ :=
    avram_p2_c_borel_original_expected_mark_measure_time_additive X
  refine ⟨μ, hRep, hAdd, ?_⟩
  intro ε hε
  rw [hRep 1 (Iic (-ε)) measurableSet_Iic]
  exact avram_p2_c_borel_original_separated_band_finite_mean
    X 1 (by norm_num) ε hε
