-- Prove2me | solution 1 for BookProof.ChapterParityChirality.chirality_iff_proj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:52.160375+00:00
-- url     : https://prove2.me/submissions/b6948121-7844-4a26-80de-e2c98034e82d

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.chirality_iff_proj
import Mathlib
import Definitions.Def_ChapterParityChirality
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
theorem solution (v : Fin 2 × Fin 4 → ℂ) :
    chi *ᵥ v = -v ↔ QLProj *ᵥ v = v := by

  have hsub : QLProj *ᵥ v = (1 / 2 : ℂ) • (v - chi *ᵥ v) := by
    simp [QLProj, Matrix.sub_mulVec, Matrix.smul_mulVec]
  constructor
  · intro h
    exact hsub.trans (by ext; norm_num [h]; ring)
  · intro hv
    rw [hsub] at hv
    have hc : v - chi *ᵥ v = (2 : ℂ) • v := by
      have := congr_arg (fun w => (2 : ℂ) • w) hv
      simpa [smul_smul] using this
    funext i
    have := congr_fun hc i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at this ⊢
    linear_combination -this
