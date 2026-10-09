-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.deriv_chi_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:52:06.577025+00:00
-- url     : https://prove2.me/submissions/59428603-c7d9-45db-95e3-bf56f4c7982b

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.deriv_chi_continuous
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_contDiff
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution : Continuous (deriv chi) := chi_contDiff.continuous_deriv (by norm_num)
