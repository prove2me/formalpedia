-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_ratio_of_regular_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:41:57.295376+00:00
-- url     : https://prove2.me/submissions/9ab30a3d-7d96-4216-acdf-932f0e3d0484

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hup0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0)
    (hdownpos : ∀ᵐ ω ∂P,
      0 < twoSidedExitDownTime X (-a) ω) :
    twoSidedExitExpectation X q a a =
      ENNReal.ofReal (W a / W a) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  calc
    twoSidedExitExpectation X q a a = 1 :=
      chat04_upper_endpoint_two_sided_exit_expectation_one
        X q a hup0 hdownpos
    _ = ENNReal.ofReal (W a / W a) := by
      simp [ne_of_gt hWa]
