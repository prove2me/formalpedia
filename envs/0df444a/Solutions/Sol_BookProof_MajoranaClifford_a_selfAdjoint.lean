-- Prove2me | solution 1 for BookProof.MajoranaClifford.a_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:24:55.275903+00:00
-- url     : https://prove2.me/submissions/b0bcd9b3-9ff4-4bab-8e72-4d727eb4ff40

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_selfAdjoint
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (v : V) : reverse (a v) = a v := by

  rw [a, reverse_ι]
