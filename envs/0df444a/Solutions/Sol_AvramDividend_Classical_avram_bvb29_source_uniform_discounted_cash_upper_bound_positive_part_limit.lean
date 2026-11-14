-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb29_source_uniform_discounted_cash_upper_bound_positive_part_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:27:43.24214+00:00
-- url     : https://prove2.me/submissions/a10b52b5-ce34-4d22-be87-f13898e3c2c2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (F K G : ℕ → ℝ) (w f k : ℝ)
    (hF : ∀ n, F n ≤ f)
    (hK : Tendsto K atTop (𝓝 k))
    (hG : Tendsto G atTop (𝓝 (0 : ℝ)))
    (hBudget : f ≤ w - k) :
    Tendsto (fun n => max (F n - (w + ((-K n) + G n))) 0)
      atTop (𝓝 (0 : ℝ))  := by
  have hInner : Tendsto
      (fun n => f - (w + ((-K n) + G n)))
      atTop (𝓝 (f - (w + ((-k) + (0 : ℝ))))) :=
    tendsto_const_nhds.sub
      (tendsto_const_nhds.add (hK.neg.add hG))
  have hBound : max (f - (w + ((-k) + (0 : ℝ)))) 0 = 0 := by
    apply max_eq_right
    linarith
  have hZero : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds
  have hUpper : Tendsto
      (fun n => max (f - (w + ((-K n) + G n))) 0)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [hBound] using hInner.max hZero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hUpper
  · intro n
    exact le_max_right _ _
  · intro n
    exact max_le_max (sub_le_sub_right (hF n) _) le_rfl
