-- Prove2me | solution 1 for FlexCommitRO.BoxExt.extremePoints_Icc
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T06:55:30.643987+00:00
-- url     : https://prove2.me/submissions/c1980a7a-e9d9-4b85-b809-4a134d23e012

import Mathlib

open Set

theorem solution (a b : ℝ) (hab : a < b) :
    (Icc a b).extremePoints ℝ = {a, b} := by
  exact extremePoints_Icc hab.le
