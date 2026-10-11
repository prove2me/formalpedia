-- Prove2me | solution 1 for BookProof.SmCar.inner_annih_left
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:56:11.790223+00:00
-- url     : https://prove2.me/submissions/ecb701e7-c61e-4546-b64c-c2cb173d4f55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.inner_annih_left
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Theorems.Thm_BookProof_SmCar_inner_creat_left
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin n) (ψ φ : FermiFock n) :
    (inner ℂ (annih i ψ) φ : ℂ) = inner ℂ ψ (creat i φ) := by

  have h := inner_creat_left i φ ψ
  have h2 := congrArg (starRingEnd ℂ) h
  rw [inner_conj_symm, inner_conj_symm] at h2
  exact h2.symm
