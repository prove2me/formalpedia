-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_eq_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:21:35.326986+00:00
-- url     : https://prove2.me/submissions/a81a2166-e079-4f42-9f0e-0744a8ec0c36

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- For unbounded variation, the zero-barrier candidate is precisely the
initial capital at every nonnegative reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) :
    barrierValue W 0 x = x := by
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hvalue : barrierValue W 0 0 = 0 :=
    barrierValue_zero_of_scale_zero W hWzero
  simpa [hvalue] using barrierValue_zero_affine_nonnegative W x hx
