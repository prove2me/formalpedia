-- Prove2me | solution 1 for BookProof.MajoranaClifford.a_anticomm_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:27:13.183654+00:00
-- url     : https://prove2.me/submissions/35ee8b16-b4b6-47e6-ba86-ecf5c7d0c20a

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
