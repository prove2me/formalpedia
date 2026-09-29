-- Prove2me | solution 1 for FamousTheorems.de_bruijn_erdos_inequality_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:15:55.193109+00:00
-- url     : https://prove2.me/submissions/25a4f120-9f68-4d40-b6bc-ff87f74cee52

import Mathlib

theorem solution (P L : Type*) [Membership P L] [Configuration.HasLines P L] [Fintype P] [Fintype L] :
    Fintype.card P ≤ Fintype.card L :=
  Configuration.HasLines.card_le P L
