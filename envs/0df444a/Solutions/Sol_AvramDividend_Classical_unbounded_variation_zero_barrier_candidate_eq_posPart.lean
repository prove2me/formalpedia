-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_eq_posPart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:25:11.56159+00:00
-- url     : https://prove2.me/submissions/8747878b-ffc1-47ca-a810-3ac5dbda5750

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_vanishes
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Unbounded variation gives a zero-barrier candidate equal to the positive
part of the reserve, including the killed negative-reserve branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) :
    barrierValue W 0 x = max x 0 := by
  by_cases hx : x < 0
  · have hnegative : barrierValue W 0 x = 0 := by
      simp [barrierValue, hx]
    rw [hnegative]
    exact (max_eq_right (le_of_lt hx)).symm
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hzero : barrierValue W 0 0 = 0 :=
      unbounded_variation_zero_barrier_candidate_vanishes X q hq W hW hnbv
    have hpositive : barrierValue W 0 x = x :=
      (barrierValue_zero_affine_nonnegative W x hx0).trans (by simp [hzero])
    simpa [max_eq_left hx0] using hpositive
