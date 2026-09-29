-- Prove2me | solution 1 for FamousTheorems.cardinality_reals_continuum_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:57:26.449581+00:00
-- url     : https://prove2.me/submissions/73d24304-724e-43e4-aab6-9320ebf4320d

import Mathlib

theorem solution : Cardinal.mk ℝ = Cardinal.continuum :=
  Cardinal.mk_real
