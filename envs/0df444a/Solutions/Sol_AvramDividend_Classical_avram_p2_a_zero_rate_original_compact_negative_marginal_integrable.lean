-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_marginal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:23:24.150946+00:00
-- url     : https://prove2.me/submissions/5e8cbf1e-c458-426e-95a2-753953f69ab8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_test_finite_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original Levy compact-negative tests are integrable at each genuine time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∀ t : ℝ≥0, Integrable (fun ω => g (X.X t ω)) P := by
  obtain ⟨ε, hε, M, hM, hBound⟩ :=
    avram_p2_j_ui_compact_negative_test_finite_envelope g hg hc hneg
  have hUniform (y : ℝ) : ‖g y‖ₑ ≤ M := by
    exact (hBound y).trans (by split_ifs <;> simp)
  intro t
  apply Integrable.of_bound ((hg.measurable.comp (hXm t)).aestronglyMeasurable) M.toReal
  filter_upwards [] with ω
  simpa [Function.comp_apply, Real.norm_eq_abs] using
    (ENNReal.toReal_mono hM (hUniform (X.X t ω)))
