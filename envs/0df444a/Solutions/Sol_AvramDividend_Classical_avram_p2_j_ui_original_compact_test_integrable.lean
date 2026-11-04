-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_compact_test_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:55:23.06487+00:00
-- url     : https://prove2.me/submissions/32f96e04-5a2b-454f-8b04-859830fe5833

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Compactly supported continuous real tests are integrable under the original Levy marginal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g)) :
    Integrable (fun ω => g (X.X t ω)) P := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  have hXm : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  apply Integrable.of_bound ((hg.measurable.comp hXm).aestronglyMeasurable) C
  exact Filter.Eventually.of_forall (fun ω => hC (X.X t ω))
