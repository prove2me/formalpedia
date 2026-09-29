-- Prove2me | solution 1 for FamousTheorems.jordan_primitive_three_cycle
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:56:13.167864+00:00
-- url     : https://prove2.me/submissions/47c46102-110c-4984-9f95-ed1a6917f203

import Mathlib

theorem solution {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPreprimitive G α)
    {g : Equiv.Perm α} (hg : g.IsThreeCycle) (hgG : g ∈ G) : alternatingGroup α ≤ G :=
  Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG hg hgG
