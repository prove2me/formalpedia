-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_original_unit_expected_mark_cutoff_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:28:51.8694+00:00
-- url     : https://prove2.me/submissions/41a6061c-fe9e-4ae3-8f22-fe26e3a51ca5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_halfline_expected_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original expected marked-jump measure is finite on a negative cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        μ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P)) ∧
      μ (Iic (-ε)) ≠ ⊤ := by
  obtain ⟨μ, hμ⟩ :=
    avram_p2_a_zero_rate_original_negative_mark_mean_measure X (1 : ℝ≥0)
  obtain ⟨C, hCpos, hBound⟩ :=
    avram_p2_a_zero_rate_original_negative_halfline_expected_finite
      X (1 : ℝ≥0) (by norm_num) ε hε
  refine ⟨μ, hμ, ?_⟩
  rw [hμ (Iic (-ε)) measurableSet_Iic]
  exact ne_of_lt (lt_of_le_of_lt (by simpa using hBound) (by simp))
