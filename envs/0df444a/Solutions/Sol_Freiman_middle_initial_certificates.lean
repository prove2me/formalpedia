-- Prove2me | solution 1 for Freiman.middle_initial_certificates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:35:26.911601+00:00
-- url     : https://prove2.me/submissions/9d7a52d7-a9cb-4bce-8c92-5e865da08138

import Theorems.Thm_Freiman_middle_initial_roots_1
import Theorems.Thm_Freiman_middle_initial_roots_2
import Theorems.Thm_Freiman_middle_initial_roots_3

open Freiman

theorem solution :
    ∀ i : Fin 15, middleRootCertificate i := by
  intro i
  by_cases h : i.val<5
  · exact middle_initial_roots_1 i (by omega) h
  · by_cases h' : i.val<10
    · exact middle_initial_roots_2 i (by omega) h'
    · exact middle_initial_roots_3 i (by omega) i.isLt
