-- Prove2me | solution 1 for FamousTheorems.kaminski_equation_bool
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:45:01.772563+00:00
-- url     : https://prove2.me/submissions/9d87b9f8-ad83-44ad-bde6-febf0274c3ca

import Mathlib

theorem solution (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x :=
  Bool.apply_apply_apply f x
