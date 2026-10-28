-- Prove2me | solution 1 for AvramDividend.Classical.time_marginal_atomless_scaled_restrict_volume_prod
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:31:07.717384+00:00
-- url     : https://prove2.me/submissions/95ea6cb8-2ab8-4e84-8389-df7655b1f26e

import Mathlib

open MeasureTheory
open scoped ENNReal
theorem solution
    (ν : Measure ℝ) [SFinite ν]
    (S : Set (ℝ × ℝ)) (c : ℝ≥0∞) :
    NullSingletonClass
      ((c • (((volume : Measure ℝ).prod ν).restrict S)).map Prod.fst) := by
  refine ⟨fun t => ?_⟩
  rw [Measure.map_apply measurable_fst (measurableSet_singleton t)]
  have hac : c • (((volume : Measure ℝ).prod ν).restrict S) ≪ (volume : Measure ℝ).prod ν :=
    (Measure.AbsolutelyContinuous.smul_left Measure.restrict_le_self.absolutelyContinuous c)
  apply hac
  have : Prod.fst ⁻¹' ({t} : Set ℝ) = ({t} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p; simp
  rw [this, Measure.prod_prod]
  simp
