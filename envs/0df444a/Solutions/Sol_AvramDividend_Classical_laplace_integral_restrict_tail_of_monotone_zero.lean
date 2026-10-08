-- Prove2me | solution 1 for AvramDividend.Classical.laplace_integral_restrict_tail_of_monotone_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:05:45.649311+00:00
-- url     : https://prove2.me/submissions/d09e0f5f-4218-45bf-8c29-e2296a8b0c31

import Mathlib

open MeasureTheory Set Filter

theorem solution
    (W : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Ici 0))
    (hWa : W a = 0) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * W x) =
      ∫ x in Ioi a, Real.exp (-β * x) * W x := by
  rw [← integral_indicator (measurableSet_Ioi :
        MeasurableSet (Ioi (0 : ℝ))),
      ← integral_indicator (measurableSet_Ioi :
        MeasurableSet (Ioi a))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hxa : x ∈ Ioi a
  · have hx0 : x ∈ Ioi (0 : ℝ) := lt_trans ha hxa
    simp [Set.indicator, hxa, hx0]
  · by_cases hx0 : x ∈ Ioi (0 : ℝ)
    · have hle : x ≤ a := le_of_not_gt hxa
      have hWx : W x = 0 := by
        have hxlt : (0 : ℝ) < x := by
          simpa only [Set.mem_Ioi] using hx0
        have hxmem : x ∈ Ici (0 : ℝ) := by
          simpa only [Set.mem_Ici] using hxlt.le
        have hamem : a ∈ Ici (0 : ℝ) := by
          simpa only [Set.mem_Ici] using ha.le
        have hxm : W x ≤ W a := hmono hxmem hamem hle
        have hxnn : 0 ≤ W x := hW x hxlt.le
        linarith
      simp [Set.indicator, hxa, hx0, hWx]
    · simp [Set.indicator, hxa, hx0]
