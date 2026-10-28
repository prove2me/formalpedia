-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedFuturePath_stationary_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:49:44.635265+00:00
-- url     : https://prove2.me/submissions/69e095ea-ca69-49ea-8e23-f32db21dfa00

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFiniteObservationVector_law
import Theorems.Thm_AvramDividend_Classical_levy_shiftedPath_law_of_all_finite_vector_laws

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X t ω) P :=
  AvramDividend.Classical.levy_shiftedPath_law_of_all_finite_vector_laws X s
    (AvramDividend.Classical.levy_shiftedFiniteObservationVector_law X s)
