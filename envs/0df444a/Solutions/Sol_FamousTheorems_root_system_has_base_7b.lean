-- Prove2me | solution 1 for FamousTheorems.root_system_has_base_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:55:29.919162+00:00
-- url     : https://prove2.me/submissions/23066ce4-c7f2-4ae2-9ca9-a1ef116be740

import Mathlib

theorem solution {ι R M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N] [Field R] [CharZero R] [Module R M]
    [Module R N] (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    Nonempty P.Base :=
  RootPairing.nonempty_base P
