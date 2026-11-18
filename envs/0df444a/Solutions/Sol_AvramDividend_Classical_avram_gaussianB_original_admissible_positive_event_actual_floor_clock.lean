-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_admissible_positive_event_actual_floor_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:01:59.592094+00:00
-- url     : https://prove2.me/submissions/9c3c9791-ef0c-479a-8d73-cc3f670a0a87

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original Gaussian floor clock is the positive horizon on a positive canonical Brownian event. -/
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
        ∀ ω ∈ E,
          sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
          (fun t : ℝ≥0 => -(riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
            Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)}) = (1 / 1000 : ℝ≥0) ∧
          (5 / 44 : ℝ) < riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω ∧
          riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω ≤ (1 / 8 : ℝ) := by
  obtain ⟨𝓕, Y, hpath, hStand, hBV, hAdm, hGeometry⟩ :=
    avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
      (1 / 1000 : ℝ≥0) (by norm_num)
  obtain ⟨E, hMeas, hPos, hTube⟩ :=
    avram_gaussianB_canonical_measurable_positive_joint_long_tube
  refine ⟨𝓕, Y, hpath, hStand, hBV, hAdm,
    E, hMeas, hPos, ?_⟩
  intro ω hω
  have hSourceTube : ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
      |Y.X t ω| ≤ (1 / 400 : ℝ) := by
    intro t ht
    have hDrift : |brownian t ω - brownian 0 ω +
        2 * (t : ℝ)| ≤ (1 / 400 : ℝ) := by
      apply avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
        (fun u => |brownian u ω - brownian 0 ω +
          2 * (u : ℝ)|) (1 / 400 : ℝ) (by
          intro u hu
          exact (hTube ω hω u hu).2) t ht
    calc
      |Y.X t ω| =
          |brownian t ω - brownian 0 ω + 2 * (t : ℝ)| :=
        congrArg abs (hpath t ω)
      _ ≤ (1 / 400 : ℝ) := hDrift
  exact hGeometry ω hSourceTube
