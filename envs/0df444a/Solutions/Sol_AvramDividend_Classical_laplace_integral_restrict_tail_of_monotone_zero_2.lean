-- Prove2me | solution 2 for AvramDividend.Classical.laplace_integral_restrict_tail_of_monotone_zero
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T17:00:48.883115+00:00
-- url     : https://prove2.me/submissions/9933f4b6-5a07-4140-a1c0-f7e9e731574b

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
  have h0 : ∀ x ∈ Ioi (0:ℝ), Real.exp (-β * x) * W x
      = (Ioi a).indicator (fun x => Real.exp (-β * x) * W x) x := by
    intro x hx
    by_cases hxa : x ∈ Ioi a
    · rw [indicator_of_mem hxa]
    · rw [indicator_of_notMem hxa]
      have h1 := hmono (mem_Ici.mpr (le_of_lt hx)) (mem_Ici.mpr ha.le) (le_of_not_gt hxa)
      rw [hWa] at h1
      have : W x = 0 := le_antisymm h1 (hW x (le_of_lt hx))
      simp [this]
  rw [setIntegral_congr_fun measurableSet_Ioi h0, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi ha.le)]
