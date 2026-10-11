-- Prove2me | solution 1 for BookProof.ChapterParityZ4.combinedParity_sq_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:34:48.368381+00:00
-- url     : https://prove2.me/submissions/d6de559f-bd23-4e2a-ace5-6371ef31d8af

-- Generated from ChapterParityZ4.lean — theorem BookProof.ChapterParityZ4.combinedParity_sq_ne_one
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParityQL
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterParityZ4
open BookProof.ChapterParityZ4


open Matrix


open BookProof.ChapterParity
open BookProof.ChapterParityQL
open BookProof.ChapterA3
open BookProof.ChapterParityZ4

theorem solution: combinedParity ^ 2 ≠ 1 := by
  intro h
  have h4 : (mgamma 0) ^ 2 = 1 := by
    have := congrArg (fun p : FieldOps => p.2.2.2) h
    simpa [combinedParity, Prod.pow_snd] using this
  have key : (Int.castRingHom ℂ).mapMatrix (mgammaZ 0 ^ 2)
      = (Int.castRingHom ℂ).mapMatrix (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    rw [map_pow, map_one]
    exact h4
  have inj : Function.Injective ((Int.castRingHom ℂ).mapMatrix :
      Matrix (Fin 4) (Fin 4) ℤ → Matrix (Fin 4) (Fin 4) ℂ) :=
    fun a b hab => Matrix.map_injective Int.cast_injective hab
  have := inj key
  revert this
  decide
