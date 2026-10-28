-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:56:08.646442+00:00
-- url     : https://prove2.me/submissions/21b34c3f-0649-4086-9cc8-66019f182879

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_mono_bounds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x y : ℝ) (hxy : x ≤ y) :
    P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ≤
    P {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} :=
  twoSidedExitBeforeDown_probability_mono_bounds X (a - y) (a - x) (-y) (-x) (by linarith) (by linarith)