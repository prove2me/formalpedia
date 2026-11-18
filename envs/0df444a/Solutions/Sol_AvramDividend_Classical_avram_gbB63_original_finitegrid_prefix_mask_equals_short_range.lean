-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:02:01.485186+00:00
-- url     : https://prove2.me/submissions/ba530b8e-7535-46ca-9916-0ed5d79b0f0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- The physical-grid strict-left stopping mask selects exactly a prefix. -/
theorem solution (m k : ℕ) (hk : k ≤ m + 1) (f : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      if i < k then f i else 0) =
    (Finset.range k).sum f := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega
