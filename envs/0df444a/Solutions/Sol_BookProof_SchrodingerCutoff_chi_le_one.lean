-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.chi_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:50:31.778216+00:00
-- url     : https://prove2.me/submissions/8583bddf-83d5-4e8e-8245-28b14d5aeeaf

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.chi_le_one
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) : chi x ≤ 1 := bump0.le_one
