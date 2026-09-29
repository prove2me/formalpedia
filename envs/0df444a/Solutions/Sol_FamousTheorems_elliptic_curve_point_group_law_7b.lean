-- Prove2me | solution 1 for FamousTheorems.elliptic_curve_point_group_law_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:14:47.039102+00:00
-- url     : https://prove2.me/submissions/8eebc423-72b7-48b2-bd1f-df21ddd7a94e

import Mathlib

theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} (P Q R : W.Point) :
    P + Q + R = P + (Q + R) ∧ P + Q = Q + P ∧ P + -P = 0 :=
  ⟨add_assoc P Q R, add_comm P Q, add_neg_cancel P⟩
