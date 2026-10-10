-- Prove2me | solution 1 for BookProof.ChapterParityHiggs.pauli2_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:54.878543+00:00
-- url     : https://prove2.me/submissions/3e1ba489-ac12-434d-b801-0d818163b3c0

-- Generated from ChapterParityHiggs.lean — solution of BookProof.ChapterParityHiggs.pauli2_map_conj
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Definitions.Def_ChapterParity
open BookProof.ChapterParityHiggs



open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution : pauli2.map (starRingEnd ℂ) = -pauli2 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli2, Matrix.map_apply, Complex.conj_I]
