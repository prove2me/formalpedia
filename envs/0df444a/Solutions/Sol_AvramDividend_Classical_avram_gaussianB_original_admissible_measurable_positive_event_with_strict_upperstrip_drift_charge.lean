-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_admissible_measurable_positive_event_with_strict_upperstrip_drift_charge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:30:45.323124+00:00
-- url     : https://prove2.me/submissions/d6557c16-0950-42d4-9d8a-b887acfac431

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_short_source_tube_of_native_joint_long_event
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_first_contact_implies_positive_original_drift_occupation_charge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original Gaussian positive event carries the missing strictly positive drift charge. -/
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
      ∃ E : Set (ℝ≥0 → ℝ), MeasurableSet E ∧
        0 < gaussianLimit E ∧
        ∀ ω ∈ E,
          0 < (2 : ℝ) * ∫ t in Ioo (0 : ℝ) (1 / 1000 : ℝ),
            (if (5 / 44 : ℝ) <
               riskProcess Y (1 / 8 : ℝ)
                 (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                 (Real.toNNReal t) ω then
                (1 : ℝ) else 0) ∂volume := by
  have hT : (0 : ℝ≥0) < (1 / 1000 : ℝ≥0) := by norm_num
  obtain ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, hGeom⟩ :=
    avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry (1 / 1000 : ℝ≥0) hT
  obtain ⟨E, hEmeas, hPos, hTube⟩ :=
    avram_gaussianB_canonical_measurable_positive_joint_long_tube
  have hShort :=
    avram_gaussianB_original_short_source_tube_of_native_joint_long_event
      𝓕 Y hpath E hTube
  refine ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, E, hEmeas, hPos, ?_⟩
  intro ω hω
  have hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |Y.X s ω| ≤ (1 / 400 : ℝ) := by
    intro s hs
    exact (hShort ω hω s hs).2.2
  have hFirst := (hGeom ω hSource).1
  have hCharge :=
    avram_gaussianB_true_first_contact_implies_positive_original_drift_occupation_charge
      (fun t : ℝ≥0 => riskProcess Y (1 / 8 : ℝ)
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)
      (5 / 44 : ℝ) (2 : ℝ) (1 / 1000 : ℝ≥0)
      hT (by norm_num) hFirst
  have hTcoe : ((1 / 1000 : ℝ≥0) : ℝ) = (1 / 1000 : ℝ) := by
    norm_num
  rw [hTcoe] at hCharge
  exact hCharge
