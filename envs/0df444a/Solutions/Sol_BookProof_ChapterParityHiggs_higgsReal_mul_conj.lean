-- Prove2me | solution 1 for BookProof.ChapterParityHiggs.higgsReal_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:13:01.614743+00:00
-- url     : https://prove2.me/submissions/1c0c6631-c30d-45b4-a0ed-e354b9208dca

-- Generated from ChapterParityHiggs.lean — solution of BookProof.ChapterParityHiggs.higgsReal_mul_conj
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Theorems.Thm_BookProof_ChapterParityHiggs_pauli2_pseudoreal
import Theorems.Thm_BookProof_ChapterParityHiggs_pseudoreal_kron_pseudoreal_real
import Definitions.Def_ChapterParity
open BookProof.ChapterParityHiggs



open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution : higgsReal * (higgsReal.map (starRingEnd ℂ)) = 1 := pseudoreal_kron_pseudoreal_real pauli2 pauli2 pauli2_pseudoreal pauli2_pseudoreal
