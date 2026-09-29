-- Prove2me | solution 1 for FamousTheorems.frattini_argument
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:27:42.338476+00:00
-- url     : https://prove2.me/submissions/843c4f53-966e-4bcf-af0b-f38872f14239

import Mathlib

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal] [Finite (Sylow p N)]
    (P : Sylow p N) :
    Subgroup.normalizer (((P : Subgroup N).map N.subtype : Subgroup G) : Set G) ⊔ N = ⊤ :=
  Sylow.normalizer_sup_eq_top P
