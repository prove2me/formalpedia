-- Prove2me | solution 1 for BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:39:23.407992+00:00
-- url     : https://prove2.me/submissions/9e35abfd-24a9-4e9b-a0ec-e3b4fe57b33f

import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Definitions.Def_ChapterHierarchicalBayesComposition
-- Generated from ChapterFiniteBayesHierarchy.lean — theorem BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append
open BookProof.ChapterHierarchicalBayesComposition
open BookProof.ChapterFiniteBayesHierarchy


open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]
theorem compKernel_assoc' {S : Type*} [Fintype S] (k₁ k₂ k₃ : S → S → ℝ) :
    compKernel (compKernel k₁ k₂) k₃ = compKernel k₁ (compKernel k₂ k₃) := by
  funext a c
  simp only [compKernel, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

theorem compKernel_id_left' {S : Type*} [Fintype S] [DecidableEq S] (k : S → S → ℝ) :
    compKernel idKernel k = k := by
  funext a c
  simp [compKernel, idKernel]

theorem solution (ks₁ ks₂ : List (S → S → ℝ)) :
    collapseKernels (ks₁ ++ ks₂) =
      compKernel (collapseKernels ks₁) (collapseKernels ks₂) := by
  induction ks₁ with
  | nil => simp [collapseKernels, compKernel_id_left']
  | cons k ks ih => simp only [List.cons_append, collapseKernels, ih, compKernel_assoc']
