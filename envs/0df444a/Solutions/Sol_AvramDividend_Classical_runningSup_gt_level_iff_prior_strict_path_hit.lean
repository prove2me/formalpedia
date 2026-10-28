-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_gt_level_iff_prior_strict_path_hit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:29:54.560801+00:00
-- url     : https://prove2.me/submissions/c56e9f00-1433-47d2-8291-0bb2e9654285

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (b : ℝ) :
    b < runningSup X t ω ↔
      ∃ s : ℝ≥0, s ≤ t ∧ b < X.X s ω := by
  obtain ⟨hmono, hle⟩ := runningSup_monotone_and_path_le X ω
  have hb : BddAbove (range fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω) := by
    refine ⟨runningSup X t ω, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (hle s.1).trans (hmono s.2.2)
  haveI : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
  rw [(runningSup_eq_rawSup_nonneg X t ω).1, lt_ciSup_iff hb]
  constructor
  · rintro ⟨s, hs⟩; exact ⟨s.1, s.2.2, hs⟩
  · rintro ⟨s, hst, hs⟩; exact ⟨⟨s, zero_le, hst⟩, hs⟩
