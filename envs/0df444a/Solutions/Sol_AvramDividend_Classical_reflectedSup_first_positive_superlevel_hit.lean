-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_first_positive_superlevel_hit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:01:26.66799+00:00
-- url     : https://prove2.me/submissions/f042c1b5-0db6-4843-aa10-4c78267c1c0f

import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero
import Theorems.Thm_AvramDividend_Classical_first_superlevel_hit_of_upperSemicontinuous
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
    (ζ : ℝ≥0) (x : ℝ) (hx : 0 < x)
    (hHit : ∃ t : ℝ≥0, t < ζ ∧ x ≤ reflectedSup X t ω) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩
        (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ x ≤ reflectedSup X T ω ∧
      ∀ s : ℝ≥0, s ≤ ζ → x ≤ reflectedSup X s ω → T ≤ s := by
  exact first_superlevel_hit_of_upperSemicontinuous
    (fun t : ℝ≥0 => reflectedSup X t ω) ζ x
    (reflectedSup_upperSemicontinuousOn_Icc X ω ζ)
    (reflectedSup_origin_eq_zero X ω) hx hHit
