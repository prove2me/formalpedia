-- Prove2me | solution 3 for BookProof.MajoranaClifford.a_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:23:47.543833+00:00
-- url     : https://prove2.me/submissions/8db8e975-45cc-4eaf-8bf3-533d507e1e87

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_add
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (v w : V) : a (v + w) = a v + a w := by

  simp [a, map_add]
