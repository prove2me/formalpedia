-- Prove2me | solution 2 for AvramDividend.Classical.avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:03:02.586693+00:00
-- url     : https://prove2.me/submissions/b5bd33c5-02ab-4a41-bb1d-53d395b77c3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
