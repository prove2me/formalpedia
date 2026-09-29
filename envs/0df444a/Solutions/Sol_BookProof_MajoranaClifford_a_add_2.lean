-- Prove2me | solution 2 for BookProof.MajoranaClifford.a_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:17:59.622092+00:00
-- url     : https://prove2.me/submissions/3c1ac687-70e4-48b6-8840-1e3c5e6be475

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_add
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (v w : V) : a (v + w) = a v + a w := by

  simp [a, map_add]
