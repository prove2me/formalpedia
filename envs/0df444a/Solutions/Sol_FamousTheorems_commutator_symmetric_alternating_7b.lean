-- Prove2me | solution 1 for FamousTheorems.commutator_symmetric_alternating_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:48:30.583987+00:00
-- url     : https://prove2.me/submissions/f164dd48-ac1e-4976-bbfd-2c0caa6fba29

import Mathlib

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (h : 5 ≤ Nat.card α) :
    commutator (Equiv.Perm α) = alternatingGroup α :=
  alternatingGroup.commutator_perm_eq h
