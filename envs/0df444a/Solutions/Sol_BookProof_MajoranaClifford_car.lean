-- Prove2me | solution 1 for BookProof.MajoranaClifford.car
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:25:51.41446+00:00
-- url     : https://prove2.me/submissions/cea57435-5e98-45f1-91c4-c097aa361d66

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.car
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
import Theorems.Thm_BookProof_MajoranaClifford_polar_Qform
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (v w : V) :
    a v * a w + a w * a v
      = algebraMap ℝ (CliffordAlgebra (Qform (V := V))) (2 * ⟪v, w⟫) := by

  rw [a, a, ι_mul_ι_add_swap, polar_Qform]
