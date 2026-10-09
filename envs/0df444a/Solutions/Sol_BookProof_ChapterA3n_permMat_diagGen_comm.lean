-- Prove2me | solution 1 for BookProof.ChapterA3n.permMat_diagGen_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:49:55.568316+00:00
-- url     : https://prove2.me/submissions/eba84a4e-2dc7-49c3-86d1-5b9d1db3e148

-- Generated from ChapterA3n.lean — solution of BookProof.ChapterA3n.permMat_diagGen_comm
import Mathlib
import Definitions.Def_ChapterA3n
import Theorems.Thm_BookProof_ChapterA3n_permMat_braiding
open BookProof.ChapterA3n



open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * diagGen A = diagGen A * permMat σ := by

  unfold diagGen
  rw [Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp σ (fun i => tensorPow (fun j => if j = i then A else 1) * permMat σ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [permMat_braiding]
  refine congrArg (· * permMat σ) (congrArg tensorPow (funext fun j => ?_))
  simp only [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
