-- Prove2me | solution 1 for FamousTheorems.archimedean_field_embeds_reals_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:15:58.586631+00:00
-- url     : https://prove2.me/submissions/26fc41d4-39f4-4160-a272-fc57307c2ec3

import Mathlib

theorem solution (α : Type*) [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] : Nonempty (α →+*o ℝ) :=
  Real.nonemptyOrderRingHom α
