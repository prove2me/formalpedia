-- Prove2me | solution 1 for BookProof.ChapterEulerComplexQuat.quat_realification_norm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:42:31.131396+00:00
-- url     : https://prove2.me/submissions/69c2f271-bc7e-436a-a6ba-f723189592a2

-- Generated from ChapterEulerComplexQuat.lean — solution of BookProof.ChapterEulerComplexQuat.quat_realification_norm
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
import Theorems.Thm_BookProof_ChapterEulerComplexQuat_quat_born_split
open BookProof.ChapterEulerComplexQuat



open scoped Quaternion BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℍ[ℝ]) :
    ∑ k, ((v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2)
      = ∑ k, qbornProb v k := by

  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [quat_born_split]
