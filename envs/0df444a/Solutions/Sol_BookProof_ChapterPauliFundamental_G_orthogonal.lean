-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.G_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:20.494973+00:00
-- url     : https://prove2.me/submissions/012e681e-6a77-40ad-a99c-eaa418285180

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.G_orthogonal
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_GZ_orthogonal
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_eq_map
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (T : Finset (Fin 4)) : G T * (G T)ᵀ = 1 := by

  have h := GZ_orthogonal T
  rw [G_eq_map]
  ext i j
  have := congrFun (congrFun (congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ =>
    M.map (Int.cast : ℤ → ℂ)) h) i) j
  simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply,
    apply_ite (Int.cast : ℤ → ℂ)] using this
