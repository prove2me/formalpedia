-- Prove2me | solution 2 for AvramDividend.Classical.levy_shiftedFuturePath_stationary_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:50:55.108381+00:00
-- url     : https://prove2.me/submissions/9d33f6f0-88dc-45fe-8c62-a50c5ccbd7fd

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFiniteObservationVector_law
import Theorems.Thm_AvramDividend_Classical_levy_shiftedPath_law_of_all_finite_vector_laws

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The full shifted future Lévy path has the same distribution as the original path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X t ω) P := by
  exact levy_shiftedPath_law_of_all_finite_vector_laws X s
    (fun J => levy_shiftedFiniteObservationVector_law X s J)
