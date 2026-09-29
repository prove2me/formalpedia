-- Prove2me | solution 1 for BookProof.MajoranaClifford.polar_Qform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:19:55.277635+00:00
-- url     : https://prove2.me/submissions/c701cefd-34fa-43e3-967c-ef2d4ac07214

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.polar_Qform
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (v w : V) : polar (Qform (V := V)) v w = 2 * ⟪v, w⟫ := by

  rw [Qform, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [innerBilin, LinearMap.mk₂_apply]
  rw [real_inner_comm w v]; ring
