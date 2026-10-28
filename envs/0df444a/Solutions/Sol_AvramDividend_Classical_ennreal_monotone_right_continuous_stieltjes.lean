-- Prove2me | solution 1 for AvramDividend.Classical.ennreal_monotone_right_continuous_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:08:39.120049+00:00
-- url     : https://prove2.me/submissions/b248dd01-d9eb-4948-b069-f4c08fbdfe97

import Mathlib
open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

theorem solution (F : ℝ → ℝ≥0∞) (hmono : Monotone F) (hright : ∀ x : ℝ, ContinuousWithinAt F (Ici x) x)
    (hbound : ∀ x : ℝ, F x ≤ 1) : ∃ S : StieltjesFunction ℝ, ∀ x : ℝ, S x = (F x).toReal := by
  have hfin : ∀ x, F x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (hbound x)
  refine ⟨{ toFun := fun x => (F x).toReal
            mono' := fun x y h => ENNReal.toReal_mono (hfin y) (hmono h)
            right_continuous' := fun x => ?_ }, fun x => rfl⟩
  exact (ENNReal.continuousAt_toReal (hfin x)).comp_continuousWithinAt (hright x)
