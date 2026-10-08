-- Prove2me | solution 2 for BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:59:44.474207+00:00
-- url     : https://prove2.me/submissions/4dffb5b3-bc46-417e-8371-254ac2aab842

-- Generated from ChapterFreeFieldConstraint.lean — theorem BookProof.FreeFieldConstraint.constraint_commutation_identity_momentum
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint

variable {R : Type*} [Ring R]

theorem solution (D H p1 : R) (hDH : bracket D H = 0) :
    bracket (bracket D p1) H = - bracket D (bracket H p1) := by   calc
    bracket (bracket D p1) H = bracket (bracket D H) p1 - bracket D (bracket H p1) := by
      unfold bracket
      noncomm_ring
    _ = - bracket D (bracket H p1) := by rw [hDH]; simp [bracket]


#print axioms solution
