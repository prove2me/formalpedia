-- Prove2me | solution 2 for BookProof.MajoranaClifford.a_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T06:24:50.754292+00:00
-- url     : https://prove2.me/submissions/4821e94a-e855-4183-9531-8edea7d614f6

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_sq
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
import Theorems.Thm_BookProof_MajoranaClifford_Qform_apply
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (v : V) : a v * a v = algebraMap ℝ (CliffordAlgebra (Qform (V := V))) ⟪v, v⟫ := by

  rw [a, ι_sq_scalar, Qform_apply]
