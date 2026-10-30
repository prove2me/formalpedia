-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_ubv_strict_interior_balance_to_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:52:49.301412+00:00
-- url     : https://prove2.me/submissions/4ec4a4ca-a402-4913-8d76-36482d75735e

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_down_clock_immediate
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_upper_endpoint_nonzero_scale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The true stopped-scale balance at positive interior reserves extends to
both endpoints, using Proved original-Lévy zero and upper boundary facts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hInterior : ∀ x : ℝ, 0 < x → x < a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv a ha
  have hInteriorRatio : ∀ y : ℝ, 0 < y → y < a →
      twoSidedExitExpectation X q a y = ENNReal.ofReal (W y / W a) := by
    intro y hy0 hya
    calc
      twoSidedExitExpectation X q a y =
          twoSidedExitExpectationCorrected X q a y :=
        chat04_twoSidedExitExpectation_eq_corrected X q a y
      _ = ENNReal.ofReal (W y / W a) :=
        chat01_unbounded_corrected_exit_ratio_of_stopped_balance
          X q hq W hW hnbv a y ha (le_of_lt hy0) (le_of_lt hya)
          (hInterior y hy0 hya)
  have hUpper : twoSidedExitExpectation X q a a =
      ENNReal.ofReal (W a / W a) :=
    avram_root29_03_upper_endpoint_nonzero_scale
      X q (le_of_lt hq) W hW a ha (ne_of_gt hWa) hInteriorRatio
  have hZero : twoSidedExitExpectation X q a 0 * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W 0) := by
    simpa only [twoSidedExitExpectation, twoSidedExitUpTime,
      twoSidedExitDownTime, sub_zero, neg_zero] using
      (chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
        X hnbv q hq W hW a ha
        (avram_root29_03_ubv_down_clock_immediate X hnbv))
  intro x hx0 hxa
  rcases eq_or_lt_of_le hx0 with hxzero | hxpos
  · subst x
    exact hZero
  · rcases lt_or_eq_of_le hxa with hxlt | hxeq
    · exact hInterior x hxpos hxlt
    · subst x
      rw [hUpper]
      simp [ne_of_gt hWa]