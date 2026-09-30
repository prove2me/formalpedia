-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.fiber_circle_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T17:35:23.190671+00:00
-- url     : https://prove2.me/submissions/8fb9163f-8923-4c74-93b8-38d443635265

import Mathlib.Data.Real.Sqrt
import Theorems.Thm_circle_trig_quadratic_pos
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

theorem solution (x y ρ Z u w z1sq c0 b1 b2 P q R2 c : ℝ)
    (hρ : R2 = ρ) (hρ0 : 0 ≤ ρ) (hxy : x ^ 2 + y ^ 2 = ρ) (hZ : 0 ≤ Z)
    (hZuw : Z ^ 2 = u ^ 2 + 4 * w ^ 2) (hu : u + Z = 2 * z1sq)
    (hc0P : c0 - 64 * z1sq * R2 ^ 2 = 4 * P) (hb : b1 ^ 2 + b2 ^ 2 = 256 * Z * q ^ 2)
    (hP : 0 < P) (hW : 16 * Z * q ^ 2 * R2 < P ^ 2) :
    0 < (c0 - 32 * u * ρ ^ 2) + b1 * x + b2 * y + (-32 * u * ρ) * (x ^ 2 - y ^ 2)
      + 2 * (-64 * w * ρ) * x * y := by
  have hxy' : x ^ 2 + y ^ 2 = Real.sqrt ρ ^ 2 := by rw [Real.sq_sqrt hρ0, hxy]
  have hS : 0 ≤ 32 * Z * ρ := by positivity
  have hkey : c0 - 32 * u * ρ ^ 2 - Real.sqrt ρ ^ 2 * (32 * Z * ρ) = 4 * P := by
    rw [Real.sq_sqrt hρ0, ← hc0P, hρ]; linear_combination (-32 * ρ ^ 2) * hu
  exact circle_trig_quadratic_pos x y (Real.sqrt ρ) (c0 - 32 * u * ρ ^ 2) b1 b2 (-32 * u * ρ)
    (-64 * w * ρ) (32 * Z * ρ) hxy' hS (by linear_combination (1024 * ρ ^ 2) * hZuw)
    (by rw [hkey]; linarith)
    (by rw [hkey, Real.sq_sqrt hρ0, hb, ← hρ]; nlinarith)
