-- Prove2me | solution 1 for FamousTheorems.subgroup_smallest_prime_index_normal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:05:09.367228+00:00
-- url     : https://prove2.me/submissions/6568f4d7-d20c-416d-a8f8-6e73baae4e4a

import Mathlib

theorem solution {G : Type*} [Group G] {H : Subgroup G} (h : H.index = (Nat.card G).minFac) : H.Normal :=
  Subgroup.normal_of_index_eq_minFac_card h
