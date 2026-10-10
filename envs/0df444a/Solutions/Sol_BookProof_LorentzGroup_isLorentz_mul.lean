-- Prove2me | solution 1 for BookProof.LorentzGroup.isLorentz_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:42:35.033056+00:00
-- url     : https://prove2.me/submissions/03076a30-a0cf-4c43-9bbf-916c2edeced2

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.isLorentz_mul
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {a b : Matrix (Fin 4) (Fin 4) ℝ}
    (ha : IsLorentz a) (hb : IsLorentz b) : IsLorentz (a * b) := by

      unfold IsLorentz at *; simp_all [ Matrix.mul_assoc ] ;
      simp_all [ ← Matrix.mul_assoc ]
