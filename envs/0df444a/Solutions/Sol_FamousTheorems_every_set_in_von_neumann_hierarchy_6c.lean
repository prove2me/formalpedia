-- Prove2me | solution 1 for FamousTheorems.every_set_in_von_neumann_hierarchy_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:58:32.252368+00:00
-- url     : https://prove2.me/submissions/88b8bc47-68c1-4c7d-8630-6f34a662121e

import Mathlib

theorem solution (x : ZFSet) : ∃ o : Ordinal, x ∈ ZFSet.vonNeumann o :=
  ZFSet.exists_mem_vonNeumann x
