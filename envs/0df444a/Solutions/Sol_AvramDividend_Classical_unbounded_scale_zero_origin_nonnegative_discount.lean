-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_zero_origin_nonnegative_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:52:53.774871+00:00
-- url     : https://prove2.me/submissions/e8040294-41b3-4c5b-a853-f04325668d00

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_zero_discount
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every nonnegative-discount q-scale function vanishes at zero when
the spectrally negative Lévy process has unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    W 0 = 0 := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    exact unbounded_scale_zero_origin_zero_discount X W hW hnbv
  · exact chat04_scale_zero_origin_of_unbounded_variation
      X hnbv q hpos W hW
