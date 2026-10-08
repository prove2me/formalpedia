-- Prove2me | solution 1 for BookProof.ChapterA3j.chir_parity_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:05:58.287996+00:00
-- url     : https://prove2.me/submissions/780d251a-8873-4629-ac63-9b7a6e77e635

import Mathlib
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3

open Matrix
open BookProof.ChapterA3
open BookProof.ChapterA3j

private theorem chir_mgamma_anticomm_local (μ : Fin 4) :
    chir * mgamma μ = -(mgamma μ * chir) := by
  have hz : mgamma5Z * mgammaZ μ = -(mgammaZ μ * mgamma5Z) := by
    fin_cases μ <;> decide
  change ((Int.castRingHom ℂ).mapMatrix mgamma5Z) *
      ((Int.castRingHom ℂ).mapMatrix (mgammaZ μ)) =
        -(((Int.castRingHom ℂ).mapMatrix (mgammaZ μ)) *
          ((Int.castRingHom ℂ).mapMatrix mgamma5Z))
  simpa only [map_mul, map_neg] using
    congrArg ((Int.castRingHom ℂ).mapMatrix) hz

theorem solution : chir * mgamma 0 = -(mgamma 0 * chir) := by
  exact chir_mgamma_anticomm_local 0

#print axioms solution
