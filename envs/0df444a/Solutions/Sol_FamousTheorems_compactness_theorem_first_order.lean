-- Prove2me | solution 1 for FamousTheorems.compactness_theorem_first_order
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:01:24.320915+00:00
-- url     : https://prove2.me/submissions/3e572a96-3f42-4540-a358-5851fab958f4

import Mathlib

theorem solution {L : FirstOrder.Language} (T : L.Theory) : T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable
