-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_B51_fixed_j9_occupation_is_full_short_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:16:30.529172+00:00
-- url     : https://prove2.me/submissions/3ea6e2e3-a726-4d36-aaad-d16600a960b3

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_NNReal_first_contact_floor_real_physical_times
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Exact original j9 Gaussian stopped occupation charge on source small-ball paths. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      (∀ ω : ℝ≥0 → ℝ,
        (∀ s : ℝ≥0, s ≤ T → |Y.X s ω| ≤ (1 / 400 : ℝ)) →
        (∫ t in Ioo (0 : ℝ) (1 : ℝ),
          (if t < (T : ℝ) ∧
              (5 / 44 : ℝ) <
              riskProcess Y (1 / 8 : ℝ)
                (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                (Real.toNNReal t) ω
            then (1 : ℝ) else 0) ∂volume) = (T : ℝ)) := by
  obtain ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, hGeom⟩ :=
    avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry T hT
  refine ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, ?_⟩
  intro ω hTube
  have hFirst := (hGeom ω hTube).1
  have hFloor : ∀ s : ℝ≥0, s < T →
      (5 / 44 : ℝ) <
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω :=
    avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
      (fun s : ℝ≥0 =>
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω)
      (5 / 44 : ℝ) T hFirst
  have hFloorReal :=
    avram_gaussianB_NNReal_first_contact_floor_real_physical_times
      (fun s : ℝ≥0 =>
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω)
      T (5 / 44 : ℝ) hFloor
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1real : (T : ℝ) ≤ 1 := by exact_mod_cast hT1
  exact avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
    (T : ℝ) (1 : ℝ) (5 / 44 : ℝ) hTreal hT1real
    (fun t : ℝ =>
      riskProcess Y (1 / 8 : ℝ)
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
        (Real.toNNReal t) ω) hFloorReal
