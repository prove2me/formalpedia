-- Prove2me | solution 1 for BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:39:42.358446+00:00
-- url     : https://prove2.me/submissions/85df23f7-f24d-42a1-8ffa-b9e1fdfffe85

import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Definitions.Def_ChapterHierarchicalBayesComposition
-- Generated from ChapterFiniteBayesHierarchy.lean — theorem BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal
open BookProof.ChapterHierarchicalBayesComposition
open BookProof.ChapterFiniteBayesHierarchy


open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]
theorem terminalMarginal_comp' {S : Type*} [Fintype S] (k₁ k₂ : S → S → ℝ) (l : S → ℝ) :
    terminalMarginal k₁ (terminalMarginal k₂ l) = terminalMarginal (compKernel k₁ k₂) l := by
  funext a
  simp only [terminalMarginal, compKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

theorem solution (ks : List (S → S → ℝ))
    (likelihood : S → ℝ) :
    nestedMarginal ks likelihood =
      terminalMarginal (collapseKernels ks) likelihood := by
  induction ks with
  | nil => funext a; simp [nestedMarginal, collapseKernels, terminalMarginal, idKernel]
  | cons k ks ih => simp only [nestedMarginal, collapseKernels, ih, terminalMarginal_comp']
