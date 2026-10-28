-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_finite_positive_height_attained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:33:44.768555+00:00
-- url     : https://prove2.me/submissions/aacd0dca-e6fd-4751-93f8-01df153f58b9

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero
import Theorems.Thm_AvramDividend_Classical_finite_excursion_height_attained_of_upperSemicontinuous
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hBound : ∀ t : ℝ≥0, t ≤ ζ → reflectedSup X t ω ≤ x)
    (hSharp : ∀ y : ℝ, y < x →
      ∃ t : ℝ≥0, t ≤ ζ ∧ y < reflectedSup X t ω) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧ reflectedSup X T ω = x := by
  exact finite_excursion_height_attained_of_upperSemicontinuous
    (fun t : ℝ≥0 => reflectedSup X t ω)
    ζ hζ
    (reflectedSup_upperSemicontinuousOn_Icc X ω ζ)
    (reflectedSup_origin_eq_zero X ω)
    hEnd x hx hBound hSharp
