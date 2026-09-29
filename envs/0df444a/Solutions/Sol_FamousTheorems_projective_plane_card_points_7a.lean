-- Prove2me | solution 1 for FamousTheorems.projective_plane_card_points_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:08:57.947982+00:00
-- url     : https://prove2.me/submissions/cec7d065-1369-400f-856b-c2c51bd56425

import Mathlib

theorem solution (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Finite L] :
    Fintype.card P = Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1 :=
  Configuration.ProjectivePlane.card_points P L
