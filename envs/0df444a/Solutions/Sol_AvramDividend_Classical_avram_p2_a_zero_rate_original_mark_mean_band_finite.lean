-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_mark_mean_band_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:58:55.721932+00:00
-- url     : https://prove2.me/submissions/f6e1e982-703d-409e-9e8a-6588d62c6719

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_halfline_expected_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source intrinsic mean mark measure is finite on every separated negative half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ μ : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        μ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤) := by
  obtain ⟨μ, hμ⟩ :=
    avram_p2_a_zero_rate_original_negative_mark_mean_measure X T
  refine ⟨μ, hμ, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hbound⟩ :=
    avram_p2_a_zero_rate_original_negative_halfline_expected_finite X T hT ε hε
  rw [hμ (Iic (-ε)) measurableSet_Iic]
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
