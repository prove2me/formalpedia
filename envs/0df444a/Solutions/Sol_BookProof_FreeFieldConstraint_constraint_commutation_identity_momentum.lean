-- Prove2me | solution 1 for BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T12:22:58.924383+00:00
-- url     : https://prove2.me/submissions/3226ef6e-eee4-42c5-9534-b5b59a310641

-- Generated from ChapterFreeFieldConstraint.lean — solution of BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
import Theorems.Thm_BookProof_FreeFieldConstraint_constraint_commutation_identity
open BookProof.FreeFieldConstraint




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (D H p1 : R) (hDH : bracket D H = 0) :
    bracket (bracket D p1) H = - bracket D (bracket H p1) := constraint_commutation_identity D H p1 hDH
