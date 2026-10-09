-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.chi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:50:30.652394+00:00
-- url     : https://prove2.me/submissions/3c807849-3775-4f16-bd58-0d4d38aeef23

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.chi_eq_zero
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution {y : ℝ} (hy : 2 ≤ |y|) : chi y = 0 := bump0.zero_of_le_dist (by simpa [Real.dist_eq, bump0] using hy)
