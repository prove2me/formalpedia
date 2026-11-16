-- Prove2me | solution 1 for DiagonalMachine.normalization
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:55:15.285207+00:00
-- url     : https://prove2.me/submissions/344b9128-b7dc-46de-a1d7-be90b32fe845

import Mathlib
open MeasureTheory Set

theorem solution (k c d dd e : ℝ) (hk : 0 < k)
    (hr : dd = k^2*d - 2*k*(2*k+1)*e) :
    (c*(2*k+1)/(2*k))*4*e = c*d - c*dd/k^2 := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  rw [hr]
  field_simp [hk0]
  <;> ring
