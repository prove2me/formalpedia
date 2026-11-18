-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB53_physical_discounted_mesh_abel_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:35:27.562667+00:00
-- url     : https://prove2.me/submissions/f34c0815-f9b4-44ea-aa48-3bd7868e49ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- Abel summation for the exact physical-grid discounted increment sequence. -/
theorem solution (m : ℕ) (a b : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      a i * (b (i + 1) - b i)) =
    a m * b (m + 1) - a 0 * b 0 +
      (Finset.range m).sum (fun i =>
        (a i - a (i + 1)) * b (i + 1)) := by
  induction m with
  | zero =>
      simp
      ring
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ]
      ring
