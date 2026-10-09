-- Prove2me | solution 1 for BookProof.ChapterA3n.tensorPow_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:48:41.516123+00:00
-- url     : https://prove2.me/submissions/704aa98d-5ba4-43ad-af84-b92aa962f8ff

-- Generated from ChapterA3n.lean — solution of BookProof.ChapterA3n.tensorPow_mul
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n



open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} (M M' : Fin N → Matrix (Fin 4) (Fin 4) ℂ) :
    tensorPow M * tensorPow M' = tensorPow (fun i => M i * M' i) := by

  ext a c;
  simp only [tensorPow, mul_apply, of_apply];
  simp only [← Finset.prod_mul_distrib];
  exact Eq.symm (Fintype.prod_sum fun i j ↦ M i (a i) j * M' i j (c i))
