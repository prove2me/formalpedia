-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_no_nonpositive_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:28:19.943656+00:00
-- url     : https://prove2.me/submissions/bae2037e-f842-4aad-bd39-c41221ebbad5

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_no_nonpositive_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (t : ℝ≥0) (θ : ℝ) :
    ((P.withDensity (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * X.X t ω) - 1) ^ 4))).map
      (fun ω => Real.exp (θ * X.X t ω))) (Iic (0 : ℝ)) = 0 := by
  exact AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_no_nonpositive_mass
    P (X.X t) (hX t) θ
