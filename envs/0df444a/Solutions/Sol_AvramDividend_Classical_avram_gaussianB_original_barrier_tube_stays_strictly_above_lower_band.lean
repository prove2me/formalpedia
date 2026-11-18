-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_barrier_tube_stays_strictly_above_lower_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:11:09.591598+00:00
-- url     : https://prove2.me/submissions/37fa1944-6399-46cb-bf85-0f6cced93ae8

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Source Gaussian equal-cap barrier remains strictly above the band on the tube. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) :
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
        ∀ t : ℝ≥0, t < T →
          (5 / 44 : ℝ) <
          riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω) := by
  obtain ⟨𝓕, Y, hpath, hStanding, hUBV, hAdm, hGeom⟩ :=
    avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry T hT
  refine ⟨𝓕, Y, hpath, hStanding, hUBV, hAdm, ?_⟩
  intro ω hTube t ht
  have hFirst := (hGeom ω hTube).1
  exact
    avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
      (fun u : ℝ≥0 => riskProcess Y (1 / 8 : ℝ)
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) u ω)
      (5 / 44 : ℝ) T hFirst t ht
