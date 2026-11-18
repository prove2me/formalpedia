-- Prove2me | solution 2 for AvramDividend.Classical.avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:10:42.021298+00:00
-- url     : https://prove2.me/submissions/e92a6b16-44a1-42f6-89a3-59522fea539c

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_with_measurable_positive_native_joint_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_long_mesh_source_tube_of_native_joint_event
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Authentic Gaussian model, original long Brownian event and mesh overshoot source bounds. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (17 / 16000 : ℝ≥0) →
          Y.X t ω = (brownian t ω - brownian 0 ω) +
            2 * (t : ℝ) ∧
          |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
          |Y.X t ω| ≤ (1 / 400 : ℝ) := by
  obtain ⟨𝓕, Y, hpath, hc, hσ, hν, hStand, hUBV, hAdm,
      E, hMeas, hPos, hTube⟩ :=
    avram_gaussianB_original_triplet_with_measurable_positive_native_joint_tube
  have hLong :=
    avram_gaussianB_original_long_mesh_source_tube_of_native_joint_event
      𝓕 Y hpath E hTube
  exact ⟨𝓕, Y, hc, hσ, hν, hStand, hUBV, hAdm,
    E, hMeas, hPos, hLong⟩
