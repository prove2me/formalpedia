-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_pre_extended_upcrossing_clock_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:00:51.150255+00:00
-- url     : https://prove2.me/submissions/39486c87-e785-497e-a117-8d7aa3300180

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (b : ℝ)
    (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) <
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞))) :
    runningSup X t ω ≤ b := by
  rw [(AvramDividend.Classical.runningSup_eq_rawSup_nonneg X t ω).1]
  haveI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
  refine ciSup_le fun s => ?_
  by_contra h
  push_neg at h
  have h1 : (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)) ≤ s.1 := iInf₂_le s.1 h
  have h2 : (s.1 : ℝ≥0∞) ≤ t := ENNReal.coe_le_coe.2 s.2.2
  exact absurd (lt_of_le_of_lt (h1.trans h2) ht) (lt_irrefl _)
