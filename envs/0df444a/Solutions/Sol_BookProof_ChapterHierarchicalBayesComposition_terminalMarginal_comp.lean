-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:09:46.221296+00:00
-- url     : https://prove2.me/submissions/52598cf1-9cc9-4159-aa4d-cd8eb240d2b9

-- Generated from ChapterHierarchicalBayesComposition.lean — solution of BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp
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
    (likelihood : C → ℝ) :
    terminalMarginal k₁ (terminalMarginal k₂ likelihood) =
      terminalMarginal (compKernel k₁ k₂) likelihood := by

  funext a
  unfold terminalMarginal compKernel
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  ring
