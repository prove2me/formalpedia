-- Prove2me | solution 1 for FamousTheorems.hermite_minkowski_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:27:05.445218+00:00
-- url     : https://prove2.me/submissions/b59f6ee8-ea48-4ec1-a90a-6a13f4956068

import Mathlib

theorem solution {K : Type*} [Field K] [NumberField K] (h : 1 < Module.finrank ℚ K) : 2 < |NumberField.discr K| :=
  NumberField.abs_discr_gt_two h
