-- Prove2me | solution 1 for AvramDividend.Classical.raw_runningSup_constant_of_future_below_previous_max
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:11:35.673522+00:00
-- url     : https://prove2.me/submissions/123ce35b-36c1-4574-9390-f4d7c9f9cb0e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Set.Basic

open AvramDividend.Classical Set
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (u v : ℝ≥0) (huv : u ≤ v)
    (hb : BddAbove (f '' Icc 0 v))
    (hBelow : ∀ t : ℝ≥0, u ≤ t → t ≤ v →
      f t ≤ sSup (f '' Icc 0 u)) :
    sSup (f '' Icc 0 v) = sSup (f '' Icc 0 u) := by
  have hsub : f '' Icc 0 u ⊆ f '' Icc 0 v := image_mono (Icc_subset_Icc le_rfl huv)
  have hbu : BddAbove (f '' Icc 0 u) := hb.mono hsub
  have hne : (f '' Icc 0 u).Nonempty := ⟨f 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩
  refine le_antisymm ?_ (csSup_le_csSup hb hne hsub)
  refine csSup_le (hne.mono hsub) ?_
  rintro _ ⟨t, ht, rfl⟩
  by_cases htu : t ≤ u
  · exact le_csSup hbu ⟨t, ⟨ht.1, htu⟩, rfl⟩
  · exact hBelow t (le_of_not_ge htu) ht.2
