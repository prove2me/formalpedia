-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayesComposition.idKernel_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:05:26.30508+00:00
-- url     : https://prove2.me/submissions/87873cda-3a70-42aa-8fa9-48a9d7b63b06

import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition
open scoped BigOperators

variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem solution : IsNonnegativeKernel (idKernel : A → A → ℝ) := by
  intro a a'
  unfold idKernel
  split_ifs <;> norm_num
