-- Prove2me | solution 1 for AvramDividend.Classical.levy_negative_before_horizon_iff_dense_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:35:46.550526+00:00
-- url     : https://prove2.me/submissions/ceb06452-f377-45fc-b2f1-915eb176f17a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_negative_right_interval
import Theorems.Thm_AvramDividend_Classical_negative_before_horizon_iff_dense_grid_of_right_negative_persistence
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (ω : Ω) (ε : ℝ≥0) :
    (∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) ↔
      (∃ m : ℕ, times m < ε ∧ X.X (times m) ω < 0) := by
  apply negative_before_horizon_iff_dense_grid_of_right_negative_persistence
    times hdense (fun t => X.X t ω)
  · intro t ht
    exact rightContinuous_negative_right_interval
      (fun s => X.X s ω) t (X.rightCont ω t) ht
