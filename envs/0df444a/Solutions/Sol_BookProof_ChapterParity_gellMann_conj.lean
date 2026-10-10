-- Prove2me | solution 1 for BookProof.ChapterParity.gellMann_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:37.130501+00:00
-- url     : https://prove2.me/submissions/9cdd36b6-4c67-4d85-a2f0-5140f98c4edd

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.gellMann_conj
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin 8) :
    (gellMann a).map (starRingEnd ℂ) = (gellMannConjSign a) • gellMann a := by

  fin_cases a <;>
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMann, gellMannConjSign, Matrix.map_apply, Matrix.smul_apply,
        Complex.conj_ofReal, map_ofNat]
