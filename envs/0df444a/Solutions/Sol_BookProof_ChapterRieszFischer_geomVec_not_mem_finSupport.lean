-- Prove2me | solution 1 for BookProof.ChapterRieszFischer.geomVec_not_mem_finSupport
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:56:32.596825+00:00
-- url     : https://prove2.me/submissions/7bffc7b6-f37f-4743-89aa-2464e0880455

-- Generated from ChapterRieszFischer.lean — theorem BookProof.ChapterRieszFischer.geomVec_not_mem_finSupport
import Mathlib
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterRieszFischer


open Filter
open scoped ENNReal
open BookProof.ChapterRieszFischer

theorem solution: geomVec ∉ FinSupport := by
  intro h
  unfold FinSupport at h
  simp only [Set.mem_setOf_eq] at h
  have hs : Function.support ((geomVec : Ell2) : ℕ → ℝ) = Set.univ := by
    ext n
    rw [Function.mem_support]
    simp only [Set.mem_univ, iff_true]
    show ((1 / 2 : ℝ)) ^ n ≠ 0
    positivity
  rw [hs] at h
  exact Set.infinite_univ h
