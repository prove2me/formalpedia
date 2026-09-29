-- Prove2me | solution 1 for FamousTheorems.successor_cardinal_regular_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:55:05.296693+00:00
-- url     : https://prove2.me/submissions/640a3527-7643-4582-bbe5-2278f366032b

import Mathlib

theorem solution {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) : (Order.succ c).IsRegular :=
  Cardinal.isRegular_succ hc
