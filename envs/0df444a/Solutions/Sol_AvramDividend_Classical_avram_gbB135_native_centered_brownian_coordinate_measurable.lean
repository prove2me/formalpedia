-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB135_native_centered_brownian_coordinate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:56:12.625983+00:00
-- url     : https://prove2.me/submissions/016f6390-0895-48aa-96ea-c5e44f82be7c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB44_native_brownian_centered_continuous_path_lift
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Each native centred Brownian coordinate is measurable on the canonical space. -/
theorem solution :
    ∀ t : ℝ≥0,
      Measurable (fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω) := by
  intro t
  have ht : Measurable (ProbabilityTheory.brownian t) :=
    ProbabilityTheory.isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec.1 t
  have hz : Measurable (ProbabilityTheory.brownian 0) :=
    ProbabilityTheory.isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec.1 0
  exact ht.sub hz
