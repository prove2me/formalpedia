-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.cliff_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:05.36599+00:00
-- url     : https://prove2.me/submissions/ee682a43-1351-4c87-a881-420e5b5564c2

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.cliff_anticomm
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (hA : IsCliffordC A) {μ ν : Fin 4} (h : μ ≠ ν) :
    A μ * A ν = -(A ν * A μ) := by

  have := hA μ ν
  rw [show minkowski μ ν = 0 by simp [minkowski, minkowskiZ, h]] at this
  simp only [mul_zero, zero_smul] at this
  linear_combination (norm := module) this
