-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.creatProj_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:30:47.665537+00:00
-- url     : https://prove2.me/submissions/f89b9c7a-fc4e-4791-8c81-3a8d03a4f5ca

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.creatProj_idem
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
import Theorems.Thm_BookProof_ChapterParityMajoranaQuant_iJ_sq
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hJ2 : J * J = -1) : creatProj J * creatProj J = creatProj J := by

  unfold creatProj
  have hK := iJ_sq J hJ2
  set K := iJ J
  rw [smul_mul_smul_comm]
  have expand : (1 - K) * (1 - K) = (2 : ℂ) • (1 - K) := by
    have h2 : (1 - K) * (1 - K) = 1 - K - K + K * K := by noncomm_ring
    rw [h2, hK]; module
  rw [expand, smul_smul]; norm_num
