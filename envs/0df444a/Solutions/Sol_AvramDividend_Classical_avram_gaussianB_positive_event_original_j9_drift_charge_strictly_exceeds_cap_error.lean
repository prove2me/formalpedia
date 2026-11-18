-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_positive_event_original_j9_drift_charge_strictly_exceeds_cap_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:16:46.754926+00:00
-- url     : https://prove2.me/submissions/bef6ab95-b010-43ef-bc8c-c488196b9b91

import Mathlib.Tactic.NormNum
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_admissible_positive_event_actual_floor_clock
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_NNReal_first_contact_floor_real_physical_times
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Measurable positive source event with actual original fixed-j9 omitted drift charge. -/
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ ω ∈ E,
          (∫ t in Ioo (0 : ℝ) (1 : ℝ),
        (if t < (1 / 1000 : ℝ) ∧
            (5 / 44 : ℝ) <
              riskProcess Y (1 / 8 : ℝ)
                (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal t) ω
         then (1 : ℝ) else 0) ∂volume) = (1 / 1000 : ℝ) ∧
          (1 / 1936 : ℝ) + (1 / 4000 : ℝ) <
            (2 : ℝ) * (∫ t in Ioo (0 : ℝ) (1 : ℝ),
        (if t < (1 / 1000 : ℝ) ∧
            (5 / 44 : ℝ) <
              riskProcess Y (1 / 8 : ℝ)
                (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal t) ω
         then (1 : ℝ) else 0) ∂volume) := by
  obtain ⟨𝓕, Y, hpath, hStanding, hUBV, hAdm,
    E, hMeas, hPos, hEvent⟩ :=
    avram_gaussianB_original_admissible_positive_event_actual_floor_clock
  refine ⟨𝓕, Y, hStanding, hUBV, hAdm,
    E, hMeas, hPos, ?_⟩
  intro ω hω
  let f : ℝ≥0 → ℝ := fun s =>
    riskProcess Y (1 / 8 : ℝ)
      (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω
  have hFirst := (hEvent ω hω).1
  have hFloor : ∀ s : ℝ≥0,
      s < (1 / 1000 : ℝ≥0) → (5 / 44 : ℝ) < f s :=
    avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
      f (5 / 44 : ℝ) (1 / 1000 : ℝ≥0) hFirst
  have hFloorReal : ∀ t : ℝ, 0 < t → t < (1 / 1000 : ℝ) →
      (5 / 44 : ℝ) < f (Real.toNNReal t) :=
    avram_gaussianB_NNReal_first_contact_floor_real_physical_times
      f (1 / 1000 : ℝ≥0) (5 / 44 : ℝ) hFloor
  have hOcc :
      (∫ t in Ioo (0 : ℝ) (1 : ℝ),
        (if t < (1 / 1000 : ℝ) ∧
            (5 / 44 : ℝ) < f (Real.toNNReal t)
          then (1 : ℝ) else 0) ∂volume) =
          (1 / 1000 : ℝ) := by
    exact avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
      (1 / 1000 : ℝ) (1 : ℝ) (5 / 44 : ℝ)
      (by norm_num) (by norm_num) (fun t => f (Real.toNNReal t))
      hFloorReal
  change ((∫ t in Ioo (0 : ℝ) (1 : ℝ),
        (if t < (1 / 1000 : ℝ) ∧
            (5 / 44 : ℝ) <
              riskProcess Y (1 / 8 : ℝ)
                (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal t) ω
         then (1 : ℝ) else 0) ∂volume) = (1 / 1000 : ℝ)) ∧
    (1 / 1936 : ℝ) + (1 / 4000 : ℝ) <
      (2 : ℝ) * (∫ t in Ioo (0 : ℝ) (1 : ℝ),
        (if t < (1 / 1000 : ℝ) ∧
            (5 / 44 : ℝ) <
              riskProcess Y (1 / 8 : ℝ)
                (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal t) ω
         then (1 : ℝ) else 0) ∂volume)
  constructor
  · exact hOcc
  · rw [hOcc]
    norm_num
