-- Prove2me | solution 1 for BookProof.MajoranaClifford.a_map_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:29:50.899004+00:00
-- url     : https://prove2.me/submissions/26bc36c0-9790-4713-862b-f2ac35acc9e6

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_map_selfAdjoint
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
import Theorems.Thm_BookProof_MajoranaClifford_a_selfAdjoint
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (T : V →ₗ[ℝ] V) (v : V) : reverse (a (T v)) = a (T v) := a_selfAdjoint (T v)
