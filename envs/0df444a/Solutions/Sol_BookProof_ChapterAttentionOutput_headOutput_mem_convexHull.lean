-- Prove2me | solution 1 for BookProof.ChapterAttentionOutput.headOutput_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T11:51:23.459132+00:00
-- url     : https://prove2.me/submissions/48b3afc4-f605-4223-8073-0db60240d928

import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput

open scoped BigOperators

open Filter Topology

noncomputable section

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) :
    headOutput beta s v ∈ convexHull ℝ (Set.range v) := by
  unfold headOutput BookProof.ChapterObservableExpectation.observableExpectation
  have hden : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  refine (convex_convexHull ℝ _).sum_mem (t := Finset.univ) ?_ ?_ ?_
  · intro j _
    unfold scoreSoftmax
    exact div_nonneg (Real.exp_pos _).le hden.le
  · unfold scoreSoftmax
    rw [← Finset.sum_div, div_self hden.ne']
  · intro j _
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
