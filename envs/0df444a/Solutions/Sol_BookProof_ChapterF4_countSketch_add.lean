-- Prove2me | solution 1 for BookProof.ChapterF4.countSketch_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:02:00.309067+00:00
-- url     : https://prove2.me/submissions/b8f858fd-df4e-47f7-9ed2-1bc5698e2dbc

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.countSketch_add
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

set_option maxHeartbeats 1000000 in
theorem solution (hash : α → κ) (s : α → Ω → ℝ) (x y : α → ℝ) (ω : Ω) (h : κ) :
    countSketch hash s (x + y) ω h = countSketch hash s x ω h + countSketch hash s y ω h := by

  unfold countSketch; simp [ mul_add, Finset.sum_add_distrib ] ;
