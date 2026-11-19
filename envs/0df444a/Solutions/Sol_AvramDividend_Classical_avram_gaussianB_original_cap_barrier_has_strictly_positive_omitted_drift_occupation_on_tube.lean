-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_cap_barrier_has_strictly_positive_omitted_drift_occupation_on_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:16:07.165041+00:00
-- url     : https://prove2.me/submissions/703bd984-1af6-48c5-84cc-ae099e7954eb

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_first_contact_implies_positive_original_drift_occupation_charge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original Gaussian source cap barrier has a strictly positive uncharged drift occupation. -/
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
        0 < (2 : ℝ) * ∫ t in Ioo (0 : ℝ) (T : ℝ),
          (if (5 / 44 : ℝ) <
              riskProcess Y (1 / 8 : ℝ)
                (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                (Real.toNNReal t) ω
            then (1 : ℝ) else 0) ∂volume) := by
  obtain ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, hGeom⟩ :=
    avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry T hT
  refine ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, ?_⟩
  intro ω hTube
  have hFirst := (hGeom ω hTube).1
  exact
    avram_gaussianB_true_first_contact_implies_positive_original_drift_occupation_charge
      (fun t : ℝ≥0 =>
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)
      (5 / 44 : ℝ) (2 : ℝ) T hT (by norm_num) hFirst
