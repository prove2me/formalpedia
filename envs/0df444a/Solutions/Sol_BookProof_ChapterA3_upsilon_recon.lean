-- Prove2me | solution 1 for BookProof.ChapterA3.upsilon_recon
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:10:34.573673+00:00
-- url     : https://prove2.me/submissions/a722479c-ab50-4238-86c1-19162a1da75c

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.upsilon_recon
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_pauli_expand
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (ν : Fin 4) :
    Tᴴ * pauliσ ν * T = ∑ μ, UpsilonC T μ ν • pauliσ μ := by

  convert pauli_expand ( Tᴴ * pauliσ ν * T ) using 1
  simp only [UpsilonC, Matrix.of_apply]
