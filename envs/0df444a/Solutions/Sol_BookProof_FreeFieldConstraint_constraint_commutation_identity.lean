-- Prove2me | solution 1 for BookProof.FreeFieldConstraint.constraint_commutation_identity
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:59:43.445293+00:00
-- url     : https://prove2.me/submissions/f7650461-a2bb-4b34-a5f8-f21f23bf5a0f

-- Generated from ChapterFreeFieldConstraint.lean — theorem BookProof.FreeFieldConstraint.constraint_commutation_identity
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint

variable {R : Type*} [Ring R]

theorem solution (D H A : R) (hDH : bracket D H = 0) :
    bracket (bracket D A) H = - bracket D (bracket H A) := by   calc
    bracket (bracket D A) H = bracket (bracket D H) A - bracket D (bracket H A) := by
      unfold bracket
      noncomm_ring
    _ = - bracket D (bracket H A) := by rw [hDH]; simp [bracket]


#print axioms solution
