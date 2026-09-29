-- Prove2me | solution 1 for FamousTheorems.schur_finite_commutators_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:40:12.455593+00:00
-- url     : https://prove2.me/submissions/e5f5f583-ed80-4116-aafb-ac8368abcc6a

import Mathlib

theorem solution (G : Type*) [Group G] [Finite (commutatorSet G)] :
    Finite (commutator G) ∧
      Nat.card (commutator G) ≤
        (Nat.card (commutatorSet G) ^ (2 * Nat.card (commutatorSet G))) ^
          (Nat.card (commutatorSet G) ^ (2 * Nat.card (commutatorSet G) + 1) + 1) :=
  ⟨inferInstance, Subgroup.card_commutator_le_of_finite_commutatorSet G⟩
