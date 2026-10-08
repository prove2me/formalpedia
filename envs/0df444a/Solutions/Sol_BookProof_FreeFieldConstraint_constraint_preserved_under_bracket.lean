-- Prove2me | solution 1 for BookProof.FreeFieldConstraint.constraint_preserved_under_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:22:24.590236+00:00
-- url     : https://prove2.me/submissions/4fa7c1f2-1100-488a-aca8-437c15101697

import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint

set_option autoImplicit false

open BookProof.FreeFieldConstraint in
theorem solution {R : Type*} [Ring R] (D H A : R)
    (hDH : bracket D H = 0) (hDA : bracket D A = 0) :
    bracket D (bracket H A) = 0 := by
  unfold bracket at *
  have h1 : D * H = H * D := sub_eq_zero.mp hDH
  have h2 : D * A = A * D := sub_eq_zero.mp hDA
  have e1 : D * (H * A) = H * A * D := by
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  have e2 : D * (A * H) = A * H * D := by
    rw [← mul_assoc, h2, mul_assoc, h1, mul_assoc]
  rw [mul_sub, sub_mul, e1, e2, sub_self]
