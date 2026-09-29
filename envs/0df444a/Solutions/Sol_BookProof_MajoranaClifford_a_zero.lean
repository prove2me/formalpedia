-- Prove2me | solution 1 for BookProof.MajoranaClifford.a_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:26:38.300396+00:00
-- url     : https://prove2.me/submissions/2949fde8-f66d-4e0c-8903-2c745a16e541

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_zero
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution : a (0 : V) = 0 := by
 simp [a]
