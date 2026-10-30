-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_full_ratio_of_interior_and_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:31:52.118637+00:00
-- url     : https://prove2.me/submissions/6885e533-6c46-4067-82b5-2bbf834030d7

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_upper_endpoint_of_interior

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Exact endpoint assembly for the Standing strict two-sided exit ratio,
without any imported Open killed stochastic theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hZero : twoSidedExitExpectation X q a 0 =
      ENNReal.ofReal (W 0 / W a))
    (hInterior : ∀ x : ℝ, 0 < x → x < a →
      twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by
  intro x hx0 hxa
  rcases eq_or_lt_of_le hx0 with hzero | hxpos
  · subst x
    exact hZero
  · rcases lt_or_eq_of_le hxa with hxlt | hxeq
    · exact hInterior x hxpos hxlt
    · subst x
      exact avram_root29_03_upper_endpoint_of_interior
        X hX q hq W hW a ha hInterior
