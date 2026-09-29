-- Prove2me | solution 1 for FamousTheorems.jordan_primitive_transposition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:41:02.314515+00:00
-- url     : https://prove2.me/submissions/97c66743-04a9-4283-a7ce-2465ac36c4c4

import Mathlib

theorem solution {α : Type*} [DecidableEq α] [Finite α] {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPreprimitive G α)
    {g : Equiv.Perm α} (hg : g.IsSwap) (hgG : g ∈ G) : G = ⊤ :=
  Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hG g hg hgG
