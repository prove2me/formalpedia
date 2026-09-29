-- Prove2me | solution 1 for FamousTheorems.perm_order_lcm_cycle_type_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:46:37.696756+00:00
-- url     : https://prove2.me/submissions/dafd72b2-e96e-42ed-90ed-9941946378b2

import Mathlib

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : σ.cycleType.lcm = orderOf σ :=
  Equiv.Perm.lcm_cycleType σ
