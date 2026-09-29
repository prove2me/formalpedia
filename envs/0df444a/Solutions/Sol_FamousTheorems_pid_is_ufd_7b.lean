-- Prove2me | solution 1 for FamousTheorems.pid_is_ufd_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:32:38.425987+00:00
-- url     : https://prove2.me/submissions/72f749ec-93f4-4944-8e09-dadd1f88473a

import Mathlib

theorem solution {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] : UniqueFactorizationMonoid R :=
  PrincipalIdealRing.to_uniqueFactorizationMonoid
