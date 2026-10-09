-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.chi_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:51:55.087902+00:00
-- url     : https://prove2.me/submissions/946a2666-81b8-4075-98b5-cbd170993f76

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.chi_differentiable
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_contDiff
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution : Differentiable ℝ chi := chi_contDiff.differentiable (by norm_num)
