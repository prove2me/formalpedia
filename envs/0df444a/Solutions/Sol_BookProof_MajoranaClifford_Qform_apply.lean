-- Prove2me | solution 1 for BookProof.MajoranaClifford.Qform_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:22:14.653045+00:00
-- url     : https://prove2.me/submissions/b553532d-4bb2-40f9-b16b-b8b06a2d74d1

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.Qform_apply
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (v : V) : Qform v = ⟪v, v⟫ := by

  simp [Qform, innerBilin, LinearMap.BilinMap.toQuadraticMap]
