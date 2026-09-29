-- Prove2me | solution 1 for FamousTheorems.matroid_rank_submodular_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:13:35.183487+00:00
-- url     : https://prove2.me/submissions/030037f3-ee11-4af5-87e6-0d8beef1e2fa

import Mathlib

theorem solution {α : Type*} (M : Matroid α) (X Y : Set α) : M.eRk (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y :=
  M.eRk_inter_add_eRk_union_le X Y
