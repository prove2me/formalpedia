-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_uniform_levy_upcrossing_clock_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:23:20.989764+00:00
-- url     : https://prove2.me/submissions/3470f53f-20a1-4e2f-808e-888988e64c53

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_stopping_times_nat_rec
import Theorems.Thm_AvramDividend_Classical_chat08_levy_detection_at_time_or_infinity_stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! Any finite prefix of a uniform sampled upcrossing grid is a stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (h : ℝ≥0) (a : ℝ) :
    ∀ n : ℕ, IsStoppingTime ℱ
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω =>
          min (if a < X.X ((k : ℝ≥0) * h) ω
            then (((k : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
            (σ ω)) n) := by
  exact chat08_finite_minimum_stopping_times_nat_rec ℱ
    (fun k ω =>
      if a < X.X ((k : ℝ≥0) * h) ω
      then (((k : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
    (fun k =>
      chat08_levy_detection_at_time_or_infinity_stopping
        X ((k : ℝ≥0) * h) a)
