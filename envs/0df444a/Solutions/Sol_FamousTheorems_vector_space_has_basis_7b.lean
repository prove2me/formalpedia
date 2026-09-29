-- Prove2me | solution 1 for FamousTheorems.vector_space_has_basis_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:54:14.112292+00:00
-- url     : https://prove2.me/submissions/5b196892-f0cc-4657-8125-da07c5c4316f

import Mathlib

theorem solution (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] : ∃ s : Set V, Nonempty (Module.Basis s K V) :=
  ⟨_, ⟨Module.Basis.ofVectorSpace K V⟩⟩
