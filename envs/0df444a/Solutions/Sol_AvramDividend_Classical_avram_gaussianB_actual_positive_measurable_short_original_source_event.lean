-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_actual_positive_measurable_short_original_source_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:02:20.726208+00:00
-- url     : https://prove2.me/submissions/4fef5f73-8e30-42c6-9557-2c5813076405

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_with_measurable_positive_native_joint_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Genuine Gaussian HJB model and positive short source event using two certified imports. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        (∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
          Y.X t ω = (brownian t ω - brownian 0 ω) +
            2 * (t : ℝ) ∧
          |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
          |Y.X t ω| ≤ (1 / 400 : ℝ)) := by
  obtain ⟨𝓕, Y, hpath, hc, hσ, hν, hStand, hUBV,
      hAdm, E, hMeas, hPos, hTube⟩ :=
    avram_gaussianB_original_triplet_with_measurable_positive_native_joint_tube
  refine ⟨𝓕, Y, hpath, hStand, hUBV, hAdm,
    E, hMeas, hPos, ?_⟩
  intro ω hω t ht
  have hC : |brownian t ω - brownian 0 ω| ≤
      (1 / 4000 : ℝ) := by
    apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
      (fun u => |brownian u ω - brownian 0 ω|)
      (1 / 4000 : ℝ) (by
        intro u hu
        exact (hTube ω hω u hu).1) t ht
  have hD : |brownian t ω - brownian 0 ω +
      2 * (t : ℝ)| ≤ (1 / 400 : ℝ) := by
    apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
      (fun u => |brownian u ω - brownian 0 ω + 2 * (u : ℝ)|)
      (1 / 400 : ℝ) (by
        intro u hu
        exact (hTube ω hω u hu).2) t ht
  refine ⟨hpath t ω, hC, ?_⟩
  exact (congrArg abs (hpath t ω)).trans_le hD
