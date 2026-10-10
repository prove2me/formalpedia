-- Prove2me | solution 1 for BookProof.ChapterPinDoubleCover.LamZ_spec_C
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:59:59.106816+00:00
-- url     : https://prove2.me/submissions/6ca995f9-f33a-417b-ad76-7969d6c8f66e

-- Generated from ChapterPinDoubleCover.lean — solution of BookProof.ChapterPinDoubleCover.LamZ_spec_C
import Mathlib
import Definitions.Def_ChapterPinDoubleCover
import Theorems.Thm_BookProof_ChapterPinDoubleCover_LamZ_spec
import Definitions.Def_ChapterA3
open BookProof.ChapterPinDoubleCover



open Matrix


open BookProof.ChapterA3
open Classical

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ S ∈ Omega, ∀ μ : Fin 4,
      mgamma μ * (Int.castRingHom ℂ).mapMatrix S
        = (Int.castRingHom ℂ).mapMatrix S * (∑ ν : Fin 4, (LamZ S) μ ν • mgamma ν) := by

  intro S hS μ
  have h := LamZ_spec S hS μ
  have h2 := congrArg (Int.castRingHom ℂ).mapMatrix h
  rw [map_mul, map_mul, map_sum] at h2
  simp only [map_zsmul] at h2
  simpa [mgamma] using h2
