-- Prove2me | solution 1 for FamousTheorems.golden_ratio_irrational_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:26:02.534301+00:00
-- url     : https://prove2.me/submissions/54ea9e41-dbb3-424a-9f33-b47f9c0de1e1

import Mathlib

theorem solution : Irrational ((1 + Real.sqrt 5) / 2) :=
  Real.goldenRatio_irrational
