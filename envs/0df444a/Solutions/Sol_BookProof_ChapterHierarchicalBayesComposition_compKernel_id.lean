-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayesComposition.compKernel_id
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:09:34.64163+00:00
-- url     : https://prove2.me/submissions/f8969865-cbcf-4b70-9e79-1fb0bdd955c0

-- Generated from ChapterHierarchicalBayesComposition.lean — solution of BookProof.ChapterHierarchicalBayesComposition.compKernel_id
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition



open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

set_option maxHeartbeats 1000000 in
theorem solution (k : A → B → ℝ) :
    compKernel k (idKernel : B → B → ℝ) = k := by

  funext a b
  simp [compKernel, idKernel]
