-- Prove2me | solution 1 for BookProof.MajoranaClifford.a_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:18:47.746655+00:00
-- url     : https://prove2.me/submissions/e6e38674-b8ad-450c-92f1-5fcb2dbb9fb5

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_smul
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (c : ℝ) (v : V) : a (c • v) = c • a v := by

  simp [a, map_smul]
