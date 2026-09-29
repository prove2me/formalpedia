-- Prove2me | solution 1 for FamousTheorems.alternating_group_simple
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:01:27.296867+00:00
-- url     : https://prove2.me/submissions/df6d8f13-3bcc-489f-9059-43599f18bf63

import Mathlib

theorem solution {α : Type*} [DecidableEq α] [Fintype α] (h : 5 ≤ Nat.card α) : IsSimpleGroup (alternatingGroup α) :=
  alternatingGroup.isSimpleGroup h
