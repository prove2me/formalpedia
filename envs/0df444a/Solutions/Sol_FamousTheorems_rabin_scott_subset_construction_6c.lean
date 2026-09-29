-- Prove2me | solution 1 for FamousTheorems.rabin_scott_subset_construction_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:56:56.157911+00:00
-- url     : https://prove2.me/submissions/0a611fcc-acf9-4a24-993d-b6f341e8f317

import Mathlib

theorem solution {α σ : Type*} (M : NFA α σ) : M.toDFA.accepts = M.accepts :=
  NFA.toDFA_correct
