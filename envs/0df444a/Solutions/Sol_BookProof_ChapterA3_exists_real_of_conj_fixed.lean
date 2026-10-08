-- Prove2me | solution 1 for BookProof.ChapterA3.exists_real_of_conj_fixed
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:21.780294+00:00
-- url     : https://prove2.me/submissions/1bc5b09a-3826-4119-817a-3c32217226f1

import Mathlib
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3 Matrix

theorem solution {N : Matrix (Fin 4) (Fin 4) ℂ}
    (hN : N.map (starRingEnd ℂ) = N) :
    ∃ M : Matrix (Fin 4) (Fin 4) ℝ, toC M = N := by
  refine ⟨fun i j => (N i j).re, ?_⟩
  ext i j
  apply Complex.ext
  · rfl
  · have hi := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => (A i j).im) hN
    simp at hi
    change 0 = (N i j).im
    linarith

#print axioms solution
