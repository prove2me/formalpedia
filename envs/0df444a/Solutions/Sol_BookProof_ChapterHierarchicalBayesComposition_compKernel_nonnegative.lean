-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:07:53.721007+00:00
-- url     : https://prove2.me/submissions/247f3858-9835-4f3f-afce-d8cc95e020fd

-- Generated from ChapterHierarchicalBayesComposition.lean — solution of BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative
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
theorem solution (k₁ : A → B → ℝ) (k₂ : B → C → ℝ)
    (h₁ : IsNonnegativeKernel k₁) (h₂ : IsNonnegativeKernel k₂) :
    IsNonnegativeKernel (compKernel k₁ k₂) := by

  intro a c
  exact Finset.sum_nonneg fun b _ => mul_nonneg (h₁ a b) (h₂ b c)
