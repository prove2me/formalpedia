-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.chi_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:50:37.089125+00:00
-- url     : https://prove2.me/submissions/15eebba5-66f7-430c-83b1-f4617f883065

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.chi_continuous
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_contDiff
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution : Continuous chi := chi_contDiff.continuous
