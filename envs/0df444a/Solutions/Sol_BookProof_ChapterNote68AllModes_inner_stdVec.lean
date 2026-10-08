-- Prove2me | solution 1 for BookProof.ChapterNote68AllModes.inner_stdVec
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:57:37.480885+00:00
-- url     : https://prove2.me/submissions/25ec55de-5ce5-419e-a6c8-535c43b5e79c

import Definitions.Def_ChapterNote68AllModes
open BookProof.ChapterNote68AllModes
open InnerProductSpace
open scoped RealInnerProductSpace

theorem solution {i j : Fin 3} (h : i ≠ j) : ⟪stdVec i, stdVec j⟫_ℝ = 0 := by
  simp [stdVec, EuclideanSpace.inner_single_left, h]

#print axioms solution
