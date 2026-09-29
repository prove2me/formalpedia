-- Prove2me | solution 1 for FamousTheorems.symmetric_group_five_not_solvable_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:05:08.97302+00:00
-- url     : https://prove2.me/submissions/8d233122-a95a-43e0-896c-a70b9cff46c7

import Mathlib

theorem solution : ¬Group.IsSolvable (Equiv.Perm (Fin 5)) :=
  Equiv.Perm.not_isSolvable_fin_5
