-- Prove2me | solution 1 for BookProof.FreeFieldConstraint.constraint_commutation_identity_field
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T12:22:04.718126+00:00
-- url     : https://prove2.me/submissions/1deecd7f-8862-4ef8-81ec-e9afbc00cfa4

-- Generated from ChapterFreeFieldConstraint.lean — solution of BookProof.FreeFieldConstraint.constraint_commutation_identity_field
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
import Theorems.Thm_BookProof_FreeFieldConstraint_constraint_commutation_identity
open BookProof.FreeFieldConstraint




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (D H φ0 : R) (hDH : bracket D H = 0) :
    bracket (bracket D φ0) H = - bracket D (bracket H φ0) := constraint_commutation_identity D H φ0 hDH
