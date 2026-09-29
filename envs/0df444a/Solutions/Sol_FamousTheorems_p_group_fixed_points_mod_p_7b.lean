-- Prove2me | solution 1 for FamousTheorems.p_group_fixed_points_mod_p_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:51:08.653713+00:00
-- url     : https://prove2.me/submissions/400ac4ac-5bd9-4157-b71d-aae382cd277b

import Mathlib

theorem solution {p : ℕ} [Fact (Nat.Prime p)] {G : Type*} [Group G] (hG : IsPGroup p G) (X : Type*) [MulAction G X]
    [Finite X] : Nat.card X ≡ Nat.card (MulAction.fixedPoints G X) [MOD p] :=
  hG.card_modEq_card_fixedPoints X
