-- Prove2me | solution 1 for BSLambda.Final.sqrt_150108_lt
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T01:30:03.708189+00:00
-- url     : https://prove2.me/submissions/2f443f3e-c346-45a2-90cb-3275d979499b

import Mathlib



theorem solution : Real.sqrt 150108 < 387.5 := by
  rw [Real.sqrt_lt' (by norm_num)] <;> norm_num
