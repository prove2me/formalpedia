-- Prove2me | solution 1 for DeletedPrimes.split_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:18:12.10864+00:00
-- url     : https://prove2.me/submissions/9e3344fc-ef4a-4c68-89f2-789a6589dd8c

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {y α ε : ℝ} (hy : 1 ≤ y) (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    (y ^ (1 / 2 : ℝ)) ^ α + y ^ (1 / 2 + 4 * ε) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) + y ^ (2 * ε)
      ≤ 3 * y ^ (α / 2 + 4 * ε) := by
  have hy0 : 0 < y := by linarith
  have h1 : (y ^ (1 / 2 : ℝ)) ^ α = y ^ (α / 2) := by
    rw [← Real.rpow_mul hy0.le]; ring_nf
  have h2 : y ^ (1 / 2 + 4 * ε) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) = y ^ (α / 2 + 4 * ε) := by
    rw [← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]; ring_nf
  rw [h1, h2]
  have h3 : y ^ (α / 2) ≤ y ^ (α / 2 + 4 * ε) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have h4 : y ^ (2 * ε) ≤ y ^ (α / 2 + 4 * ε) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  linarith
end DeletedPrimes
