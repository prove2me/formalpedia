-- Prove2me | solution 1 for FamousTheorems.perm_conj_iff_cycle_type_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:43:57.023609+00:00
-- url     : https://prove2.me/submissions/b8ad72b4-73d7-4cc2-9db7-26b4240f6055

import Mathlib

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) : IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
  Equiv.Perm.isConj_iff_cycleType_eq
