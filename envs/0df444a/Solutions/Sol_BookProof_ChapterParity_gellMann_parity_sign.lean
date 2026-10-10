-- Prove2me | solution 1 for BookProof.ChapterParity.gellMann_parity_sign
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:38.538663+00:00
-- url     : https://prove2.me/submissions/cd507ea4-2057-4ad8-bfea-5627af5ad798

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.gellMann_parity_sign
import Mathlib
import Definitions.Def_ChapterParity
import Theorems.Thm_BookProof_ChapterParity_gellMann_conj
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin 8) :
    -((gellMann a).map (starRingEnd ℂ)) = (-(gellMannConjSign a)) • gellMann a := by

  rw [gellMann_conj, neg_smul]
