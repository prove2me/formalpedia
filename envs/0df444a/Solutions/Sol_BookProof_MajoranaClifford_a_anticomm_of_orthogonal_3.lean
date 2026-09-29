-- Prove2me | solution 3 for BookProof.MajoranaClifford.a_anticomm_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:32:51.654085+00:00
-- url     : https://prove2.me/submissions/a771e7e2-a79b-418d-b82f-5b8786905ba8

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_anticomm_of_orthogonal
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
import Theorems.Thm_BookProof_MajoranaClifford_car
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution {v w : V} (h : ⟪v, w⟫ = (0 : ℝ)) :
    a v * a w + a w * a v = 0 := by

  rw [car, h]; simp
