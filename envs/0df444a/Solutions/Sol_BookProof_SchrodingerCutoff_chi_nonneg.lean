-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.chi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:50:32.865161+00:00
-- url     : https://prove2.me/submissions/efa212e8-f1f9-4056-9f56-5f9e62136f0d

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.chi_nonneg
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) : 0 ≤ chi x := bump0.nonneg
