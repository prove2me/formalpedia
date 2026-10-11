-- Prove2me | solution 1 for BookProof.ChapterPinOmega.noncommC
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:45:37.74749+00:00
-- url     : https://prove2.me/submissions/fa924375-a38e-466c-9453-bd11e38a7cc2

-- Generated from ChapterPinOmega.lean — theorem BookProof.ChapterPinOmega.noncommC
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterA3
open BookProof.ChapterPinDoubleCover
open BookProof.ChapterPinOmega


open Matrix


open BookProof.ChapterA3
open BookProof.ChapterPinOmega

theorem solution: qiC * qjC ≠ qjC * qiC := by
  intro h
  have key : (Int.castRingHom ℂ).mapMatrix (mgammaZ 0 * (-(mgammaZ 0 * mgamma5Z)))
      = (Int.castRingHom ℂ).mapMatrix ((-(mgammaZ 0 * mgamma5Z)) * mgammaZ 0) := by
    simp only [map_mul, map_neg]
    exact h
  have inj : Function.Injective ((Int.castRingHom ℂ).mapMatrix :
      Matrix (Fin 4) (Fin 4) ℤ → Matrix (Fin 4) (Fin 4) ℂ) :=
    fun a b hab => Matrix.map_injective Int.cast_injective hab
  have := inj key
  revert this
  decide
