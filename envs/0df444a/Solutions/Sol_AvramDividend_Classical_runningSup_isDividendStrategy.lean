-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_isDividendStrategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:01:08.625274+00:00
-- url     : https://prove2.me/submissions/85447bc8-02fd-4fd1-815d-24a8ffd9e0ac

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IsDividendStrategy 𝓕 (runningSup X) := by
  have hEq : barrierStrategy X (0 : ℝ) 0 = runningSup X := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  rw [← hEq]
  exact barrierStrategy_isDividendStrategy_nonnegative_barrier
    X 0 0 le_rfl le_rfl
