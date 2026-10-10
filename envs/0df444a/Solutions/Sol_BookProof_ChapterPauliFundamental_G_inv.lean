-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.G_inv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:21.656575+00:00
-- url     : https://prove2.me/submissions/b28757cb-427f-470e-a843-665b0779debf

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.G_inv
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_orthogonal
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (T : Finset (Fin 4)) : (G T)⁻¹ = (G T)ᵀ := Matrix.inv_eq_right_inv (G_orthogonal T)
