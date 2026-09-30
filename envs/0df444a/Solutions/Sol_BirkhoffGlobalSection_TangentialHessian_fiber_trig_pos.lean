-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.fiber_trig_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:19.286166+00:00
-- url     : https://prove2.me/submissions/fe865198-4808-480b-b71e-af989a8b04c7

import Theorems.Thm_circle_trig_quadratic_pos
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Matrix in
theorem solution (x y F l00 l01 l11 v0 v1 a b : ℝ) (hc : x ^ 2 + y ^ 2 = F)
    (hG : 0 < F * (l00 * l11 - l01 ^ 2) + (l11 * v0 ^ 2 - 2 * l01 * v0 * v1 + l00 * v1 ^ 2)
      - 16 * F ^ 2 * (a ^ 2 + b ^ 2))
    (hW : F * ((F * (l11 * (-4 * b) - 2 * l01 * (-4 * a) + l00 * (-12 * b))
          + ((-12 * b) * v0 ^ 2 - 2 * (-4 * a) * v0 * v1 + (-4 * b) * v1 ^ 2)) ^ 2
        + (F * (l11 * (12 * a) - 2 * l01 * (4 * b) + l00 * (4 * a))
          + ((4 * a) * v0 ^ 2 - 2 * (4 * b) * v0 * v1 + (12 * a) * v1 ^ 2)) ^ 2)
      < (F * (l00 * l11 - l01 ^ 2) + (l11 * v0 ^ 2 - 2 * l01 * v0 * v1 + l00 * v1 ^ 2)
          - 16 * F ^ 2 * (a ^ 2 + b ^ 2)) ^ 2) :
    0 < (x ^ 2 + y ^ 2) *
          ((l00 + x * (-4 * b) + y * (12 * a)) * (l11 + x * (-12 * b) + y * (4 * a))
            - (l01 + x * (-4 * a) + y * (4 * b)) ^ 2) +
        ((l11 + x * (-12 * b) + y * (4 * a)) * v0 ^ 2
          - 2 * (l01 + x * (-4 * a) + y * (4 * b)) * v0 * v1
          + (l00 + x * (-4 * b) + y * (12 * a)) * v1 ^ 2) := by
  have hF : 0 ≤ F := by rw [← hc]; positivity
  have hR2 : Real.sqrt F ^ 2 = F := Real.sq_sqrt hF
  set G := F * (l00 * l11 - l01 ^ 2) + (l11 * v0 ^ 2 - 2 * l01 * v0 * v1 + l00 * v1 ^ 2)
      - 16 * F ^ 2 * (a ^ 2 + b ^ 2) with hGdef
  set S := 32 * F * (a ^ 2 + b ^ 2) with hSdef
  have hk : G + F * S - Real.sqrt F ^ 2 * S = G := by rw [hR2]; ring
  have key := circle_trig_quadratic_pos x y (Real.sqrt F) (G + F * S)
    (F * (l11 * (-4 * b) - 2 * l01 * (-4 * a) + l00 * (-12 * b))
      + ((-12 * b) * v0 ^ 2 - 2 * (-4 * a) * v0 * v1 + (-4 * b) * v1 ^ 2))
    (F * (l11 * (12 * a) - 2 * l01 * (4 * b) + l00 * (4 * a))
      + ((4 * a) * v0 ^ 2 - 2 * (4 * b) * v0 * v1 + (12 * a) * v1 ^ 2))
    (-32 * F * (a ^ 2 - b ^ 2)) (-64 * F * a * b) S
    (by rw [hR2, hc]) (by positivity) (by rw [hSdef]; ring)
    (by rw [hk]; exact hG) (by rw [hk, hR2]; exact hW)
  have e : (x ^ 2 + y ^ 2) *
          ((l00 + x * (-4 * b) + y * (12 * a)) * (l11 + x * (-12 * b) + y * (4 * a))
            - (l01 + x * (-4 * a) + y * (4 * b)) ^ 2) +
        ((l11 + x * (-12 * b) + y * (4 * a)) * v0 ^ 2
          - 2 * (l01 + x * (-4 * a) + y * (4 * b)) * v0 * v1
          + (l00 + x * (-4 * b) + y * (12 * a)) * v1 ^ 2)
      = G + F * S
        + (F * (l11 * (-4 * b) - 2 * l01 * (-4 * a) + l00 * (-12 * b))
          + ((-12 * b) * v0 ^ 2 - 2 * (-4 * a) * v0 * v1 + (-4 * b) * v1 ^ 2)) * x
        + (F * (l11 * (12 * a) - 2 * l01 * (4 * b) + l00 * (4 * a))
          + ((4 * a) * v0 ^ 2 - 2 * (4 * b) * v0 * v1 + (12 * a) * v1 ^ 2)) * y
        + (-32 * F * (a ^ 2 - b ^ 2)) * (x ^ 2 - y ^ 2) + 2 * (-64 * F * a * b) * x * y := by
    rw [hGdef, hSdef]
    linear_combination
      ((l00 + x * (-4 * b) + y * (12 * a)) * (l11 + x * (-12 * b) + y * (4 * a))
        - (l01 + x * (-4 * a) + y * (4 * b)) ^ 2 + 16 * F * (a ^ 2 + b ^ 2)) * hc
  rw [e]
  exact key
