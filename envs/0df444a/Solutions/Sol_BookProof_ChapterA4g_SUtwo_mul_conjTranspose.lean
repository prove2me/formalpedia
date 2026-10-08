-- Prove2me | solution 1 for BookProof.ChapterA4g.SUtwo_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:45:28.362841+00:00
-- url     : https://prove2.me/submissions/5b155c98-31e5-4200-a321-5c3a4df6c4a1

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SUtwo_mul_conjTranspose
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4c
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 4000000 in
theorem solution {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SUtwo) : S * Sᴴ = 1 := by
  exact mul_eq_one_comm.mp hS.2

#print axioms solution
