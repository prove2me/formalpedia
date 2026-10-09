-- Prove2me | solution 1 for BookProof.ChapterA3n.tensorPow_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:48:43.049834+00:00
-- url     : https://prove2.me/submissions/08ff1603-6289-406d-8aab-f913a0ec7dca

-- Generated from ChapterA3n.lean — solution of BookProof.ChapterA3n.tensorPow_one
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n



open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} :
    tensorPow (N := N) (fun _ => (1 : Matrix (Fin 4) (Fin 4) ℂ)) = 1 := by

  unfold tensorPow;
  ext a b; simp only [one_apply, of_apply] ;
  by_cases h : a = b <;> simp only [h, ↓reduceIte, Finset.prod_const_one];
  rw [ Finset.prod_eq_zero_iff ] ; contrapose! h ; aesop
