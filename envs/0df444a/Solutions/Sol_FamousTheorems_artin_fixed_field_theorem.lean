-- Prove2me | solution 1 for FamousTheorems.artin_fixed_field_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:02:39.517443+00:00
-- url     : https://prove2.me/submissions/26c2243e-94c1-444e-91fb-f418cc9a0c51

import Mathlib

theorem solution (G F : Type*) [Group G] [Field F] [MulSemiringAction G F] [Fintype G] [FaithfulSMul G F] :
    Module.finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  FixedPoints.finrank_eq_card G F
