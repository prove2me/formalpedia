-- Prove2me | solution 1 for FamousTheorems.perm_generated_by_transpositions_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:43:57.04625+00:00
-- url     : https://prove2.me/submissions/20566d92-1fa9-4059-9278-b195f150c84d

import Mathlib

theorem solution (α : Type*) [DecidableEq α] [Finite α] : Subgroup.closure {σ : Equiv.Perm α | σ.IsSwap} = ⊤ :=
  Equiv.Perm.closure_isSwap
