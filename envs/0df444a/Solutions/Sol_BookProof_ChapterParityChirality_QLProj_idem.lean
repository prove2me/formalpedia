-- Prove2me | solution 1 for BookProof.ChapterParityChirality.QLProj_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:48.347777+00:00
-- url     : https://prove2.me/submissions/7c44364a-b9d5-4cdc-af86-dee150055819

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.QLProj_idem
import Mathlib
import Definitions.Def_ChapterParityChirality
import Theorems.Thm_BookProof_ChapterParityChirality_chi_sq
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParityChirality



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution : QLProj * QLProj = QLProj := by

  have hexp : (1 - chi) * (1 - chi) = (2 : ℂ) • (1 - chi) := by
    have h : (1 - chi) * (1 - chi) = 1 - chi - chi + chi * chi := by noncomm_ring
    rw [h, chi_sq]; module
  rw [QLProj, Matrix.smul_mul, Matrix.mul_smul, hexp, smul_smul, smul_smul]
  norm_num
