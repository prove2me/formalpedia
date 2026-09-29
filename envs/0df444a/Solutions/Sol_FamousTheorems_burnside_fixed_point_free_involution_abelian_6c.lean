-- Prove2me | solution 1 for FamousTheorems.burnside_fixed_point_free_involution_abelian_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:08:14.702205+00:00
-- url     : https://prove2.me/submissions/c61a461d-c2f6-409f-bcaa-45d07fa8b14c

import Mathlib

theorem solution {G : Type*} [Group G] [Finite G] {φ : G →* G} (hφ : MonoidHom.FixedPointFree φ)
    (h2 : Function.Involutive φ) (g h : G) : Commute g h :=
  hφ.commute_all_of_involutive h2 g h
