-- Prove2me | solution 1 for FamousTheorems.int_subgroup_cyclic_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:19:20.006414+00:00
-- url     : https://prove2.me/submissions/b6a5e009-c911-4236-bc1f-9a72377885cf

import Mathlib

theorem solution (H : AddSubgroup ℤ) : ∃ a : ℤ, H = AddSubgroup.closure {a} :=
  Int.subgroup_cyclic H
