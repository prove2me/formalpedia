-- Prove2me | solution 1 for FamousTheorems.kleene_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:22:06.522374+00:00
-- url     : https://prove2.me/submissions/eee7bc50-e36d-4a7f-941f-3e322838aa76

import Mathlib

theorem solution {α : Type*} [CompleteLattice α] (f : α →o α) (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
    OrderHom.lfp f = ⨆ n : ℕ, f^[n] ⊥ :=
  fixedPoints.lfp_eq_sSup_iterate f hf
