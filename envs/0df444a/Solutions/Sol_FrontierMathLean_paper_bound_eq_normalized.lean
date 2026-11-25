-- Prove2me | solution 1 for FrontierMathLean.paper_bound_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:42:24.250016+00:00
-- url     : https://prove2.me/submissions/97c92ffb-7cac-44ca-82b6-8c6bbb7cce83

import Definitions.Def_FrontierMathLean_AbstractInequality
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_ThreeTermInequality

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (k : ℕ) :
    (5 * (u * v) ^ k + 2 * v ^ (2 * k) + 2 * u ^ (2 * k)) /
        (u * v) ^ k =
      5 + 2 * ((v / u) ^ k + ((v / u) ^ k)⁻¹) := by
  have hpowv : v ^ (2 * k) = (v ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  have hpowu : u ^ (2 * k) = (u ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  rw [hpowv, hpowu, mul_pow, div_pow]
  field_simp [hu.ne', hv.ne']
  ring
end FrontierMathLean
