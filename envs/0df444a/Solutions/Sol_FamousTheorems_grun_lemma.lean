-- Prove2me | solution 1 for FamousTheorems.grun_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:36:30.430909+00:00
-- url     : https://prove2.me/submissions/1278d908-be4a-4ab5-bd3f-f1a7e25ce8a0

import Mathlib

theorem solution (G : Type*) [Group G] [Group.IsPerfect G] : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ :=
  Group.IsPerfect.center_quotient_center_eq_bot G
