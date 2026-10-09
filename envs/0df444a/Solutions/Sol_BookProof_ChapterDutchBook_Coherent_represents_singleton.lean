-- Prove2me | solution 1 for BookProof.ChapterDutchBook.Coherent.represents_singleton
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:15.954189+00:00
-- url     : https://prove2.me/submissions/3793177f-5009-4a5a-943a-2736981151a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.Coherent.represents_singleton
import Mathlib
import Definitions.Def_ChapterDutchBook
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_empty
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_additive
open BookProof.ChapterDutchBook



open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

variable {Ω : Type*} [DecidableEq Ω]

set_option maxHeartbeats 1000000 in
theorem solution {Pr : Finset Ω → ℝ} (h : Coherent Pr)
    (A : Finset Ω) : Pr A = ∑ ω ∈ A, Pr {ω} := by

  refine Finset.induction_on A ?_ ?_
  · simp [h.empty]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.insert_eq,
        h.additive (Finset.disjoint_singleton_left.mpr ha), ih]
