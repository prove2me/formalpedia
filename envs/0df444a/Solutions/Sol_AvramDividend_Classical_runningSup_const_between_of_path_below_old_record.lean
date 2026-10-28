-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_const_between_of_path_below_old_record
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:14:32.704534+00:00
-- url     : https://prove2.me/submissions/a1dcc824-a2ca-4c6d-8baf-22e21c5f813c

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u v : ℝ≥0) (huv : u ≤ v)
    (hBelow : ∀ t : ℝ≥0, u ≤ t → t ≤ v →
      X.X t ω ≤ runningSup X u ω) :
    runningSup X v ω = runningSup X u ω := by
  obtain ⟨hmono, hle⟩ := runningSup_monotone_and_path_le X ω
  refine le_antisymm ?_ (hmono huv)
  rw [(runningSup_eq_rawSup_nonneg X v ω).1]
  haveI : Nonempty (Icc (0 : ℝ≥0) v) := ⟨⟨0, le_rfl, zero_le⟩⟩
  refine ciSup_le (fun s => ?_)
  by_cases hsu : s.1 ≤ u
  · exact (hle s.1).trans (hmono hsu)
  · exact hBelow s.1 (le_of_not_ge hsu) s.2.2
