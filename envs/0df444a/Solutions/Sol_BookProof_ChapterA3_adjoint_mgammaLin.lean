-- Prove2me | solution 1 for BookProof.ChapterA3.adjoint_mgammaLin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:00.432853+00:00
-- url     : https://prove2.me/submissions/8089faa3-4cf5-4958-a8ae-08894f6ed953

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.adjoint_mgammaLin
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_mgamma_conjTranspose
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    LinearMap.adjoint (mgammaLin μ) = (if μ = 0 then (-1 : ℂ) else 1) • mgammaLin μ := by

  rw [mgammaLin, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, mgamma_conjTranspose]
  split_ifs <;> simp []
