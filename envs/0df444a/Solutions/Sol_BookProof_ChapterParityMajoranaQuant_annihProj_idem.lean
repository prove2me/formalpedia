-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.annihProj_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:27:08.092404+00:00
-- url     : https://prove2.me/submissions/b3b35b42-ea1a-46ea-9855-3e614668d00d

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.annihProj_idem
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
import Theorems.Thm_BookProof_ChapterParityMajoranaQuant_iJ_sq
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hJ2 : J * J = -1) : annihProj J * annihProj J = annihProj J := by

  unfold annihProj
  have hK := iJ_sq J hJ2
  set K := iJ J
  rw [smul_mul_smul_comm]
  have expand : (1 + K) * (1 + K) = (2 : ℂ) • (1 + K) := by
    have h2 : (1 + K) * (1 + K) = 1 + K + K + K * K := by noncomm_ring
    rw [h2, hK]; module
  rw [expand, smul_smul]; norm_num
