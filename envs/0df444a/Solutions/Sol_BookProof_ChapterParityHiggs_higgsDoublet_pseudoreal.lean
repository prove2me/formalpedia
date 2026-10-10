-- Prove2me | solution 1 for BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:57.74167+00:00
-- url     : https://prove2.me/submissions/2dba24b6-7ef0-473d-af23-962b380ab421

-- Generated from ChapterParityHiggs.lean — solution of BookProof.ChapterParityHiggs.higgsDoublet_pseudoreal
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Theorems.Thm_BookProof_ChapterParityHiggs_realityOp_realityOp
import Theorems.Thm_BookProof_ChapterParityHiggs_pauli2_pseudoreal
import Definitions.Def_ChapterParity
open BookProof.ChapterParityHiggs



open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 2 → ℂ) :
    realityOp pauli2 (realityOp pauli2 v) = -v := by

  rw [realityOp_realityOp, pauli2_pseudoreal]
  ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
