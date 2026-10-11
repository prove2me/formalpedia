-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.coordComboSum_sqCoef
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:56.093105+00:00
-- url     : https://prove2.me/submissions/77168acf-67ea-41b8-a1e0-14a9c740c609

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.coordComboSum_sqCoef
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Theorems.Thm_BookProof_SqueezedGaussStates_sqCoef_of_le
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : ℝ) (M : ℕ) : coordComboSum (sqCoef v M) 0 M = Vsum v M := by

  rw [coordComboSum, Vsum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [sqCoef_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), Acoef]
  simp
