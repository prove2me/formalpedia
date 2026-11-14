-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_compensated_cash_positive_part_lim_zero_of_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:06.565872+00:00
-- url     : https://prove2.me/submissions/7d9cec22-c426-4764-9a50-cbdb07ea4a1b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (F K G : ℕ → ℝ) (w f k : ℝ)
    (hF : Tendsto F atTop (𝓝 f))
    (hK : Tendsto K atTop (𝓝 k))
    (hG : Tendsto G atTop (𝓝 (0 : ℝ)))
    (hBudget : f ≤ w - k) :
    Tendsto (fun n => max (F n - (w + ((-K n) + G n))) 0)
      atTop (𝓝 (0 : ℝ))  := by
  have hInner :
      Tendsto (fun n => w + (-K n + G n))
        atTop (𝓝 (w + (-k + 0))) :=
    tendsto_const_nhds.add (hK.neg.add hG)
  have hGap := hF.sub hInner
  have hMax := hGap.max (tendsto_const_nhds (x := (0 : ℝ)))
  have hNonpos : f - (w + (-k + 0)) ≤ 0 := by
    linarith
  have hLimit : max (f - (w + (-k + 0))) (0 : ℝ) = 0 :=
    max_eq_right hNonpos
  simpa only [hLimit] using hMax
