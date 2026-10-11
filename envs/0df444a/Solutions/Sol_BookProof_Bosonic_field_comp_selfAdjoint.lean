-- Prove2me | solution 1 for BookProof.Bosonic.field_comp_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:48:48.405444+00:00
-- url     : https://prove2.me/submissions/3e4da66f-8f98-4f6a-a874-6f4c29ca3899

-- Generated from ChapterBosonicCCR.lean — solution of BookProof.Bosonic.field_comp_selfAdjoint
import Mathlib
import Definitions.Def_ChapterBosonicCCR
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_selfAdjoint
import Definitions.Def_ChapterStoneConverse
open BookProof.Bosonic



open RealInnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Algebra ℝ R]
  [IsScalarTower ℝ ℂ R] [StarModule ℂ R]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Algebra ℝ R]
  [IsScalarTower ℝ ℂ R] [StarModule ℂ R]
variable {J : V →ₗ[ℝ] V} {a : V →ₗ[ℝ] R}

set_option maxHeartbeats 1000000 in
theorem solution (h : BosonicCCR J a) (T : V →ₗ[ℝ] V) (v : V) :
    star (a (T v)) = a (T v) := h.selfAdjoint (T v)
