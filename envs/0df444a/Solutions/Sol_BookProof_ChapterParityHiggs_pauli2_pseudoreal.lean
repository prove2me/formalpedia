-- Prove2me | solution 1 for BookProof.ChapterParityHiggs.pauli2_pseudoreal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:56.343483+00:00
-- url     : https://prove2.me/submissions/60bb7dea-0de7-4808-90f5-8d48ce51b95c

-- Generated from ChapterParityHiggs.lean — solution of BookProof.ChapterParityHiggs.pauli2_pseudoreal
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Theorems.Thm_BookProof_ChapterParityHiggs_pauli2_map_conj
import Theorems.Thm_BookProof_ChapterParity_pauli2_sq
import Definitions.Def_ChapterParity
open BookProof.ChapterParityHiggs



open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution : pauli2 * (pauli2.map (starRingEnd ℂ)) = -1 := by

  rw [pauli2_map_conj, Matrix.mul_neg, pauli2_sq]
