-- Prove2me | solution 1 for FamousTheorems.alternating_generated_by_three_cycles_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:45:36.964326+00:00
-- url     : https://prove2.me/submissions/c2e763e5-0c69-40bf-9b69-7ee76ed8417d

import Mathlib

theorem solution (α : Type*) [Fintype α] [DecidableEq α] :
    Subgroup.closure {σ : Equiv.Perm α | σ.IsThreeCycle} = alternatingGroup α :=
  Equiv.Perm.closure_three_cycles_eq_alternating
