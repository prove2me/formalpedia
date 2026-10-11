-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:33:25.009179+00:00
-- url     : https://prove2.me/submissions/4005615c-19c8-4f61-a5fc-3e16fdb56849

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    0 < ∑ l, Real.exp (beta * s l) := Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
