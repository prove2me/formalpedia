-- Prove2me | solution 1 for AvramDividend.Classical.time_marginal_atomless_of_ac_volume_prod
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:26:32.122992+00:00
-- url     : https://prove2.me/submissions/2605dce2-54c8-4c17-86f0-1b63483c6a9f

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (ν : Measure ℝ) [SFinite ν]
    (η : Measure (ℝ × ℝ))
    (hη : η ≪ ((volume : Measure ℝ).prod ν)) :
    NullSingletonClass (η.map Prod.fst) := by
  refine ⟨fun t => ?_⟩
  rw [Measure.map_apply measurable_fst (measurableSet_singleton t)]
  apply hη
  have : Prod.fst ⁻¹' ({t} : Set ℝ) = ({t} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext p; simp
  rw [this, Measure.prod_prod]
  simp
