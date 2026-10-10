-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.G_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:19.504326+00:00
-- url     : https://prove2.me/submissions/b1e0f0a9-9a4d-469b-ac04-101883678b6e

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.G_eq_map
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (T : Finset (Fin 4)) : G T = (GZ T).map (Int.cast) := by

  have h : ∀ l : List (Fin 4), gp mgamma l = (gpZ mgammaZ l).map (Int.cast) := by
    intro l
    induction l with
    | nil =>
        ext i j
        by_cases hij : i = j <;> simp [gp, gpZ, Matrix.one_apply, hij]
    | cons a t ih =>
        change mgamma a * gp mgamma t = _
        rw [ih, mgamma]
        ext i j
        simp [gpZ, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [G, gpF, GZ, h]
