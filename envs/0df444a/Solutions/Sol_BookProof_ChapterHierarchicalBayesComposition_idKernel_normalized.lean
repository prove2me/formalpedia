-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayesComposition.idKernel_normalized
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:10:19.615969+00:00
-- url     : https://prove2.me/submissions/e7b6a723-4652-4ebf-9601-843cf6687088

import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition
open scoped BigOperators

variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem solution : IsNormalizedKernel (idKernel : A → A → ℝ) := by
  intro a
  simp only [IsNormalizedKernel, idKernel]
  rw [Finset.sum_ite_eq (s := (Finset.univ : Finset A)) (a := a) (b := fun _ => (1 : ℝ))]
  simp
