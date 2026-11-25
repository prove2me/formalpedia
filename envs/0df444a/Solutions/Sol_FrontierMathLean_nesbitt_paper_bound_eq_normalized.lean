-- Prove2me | solution 1 for FrontierMathLean.nesbitt_paper_bound_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:49.095047+00:00
-- url     : https://prove2.me/submissions/7c717c5f-2d7e-4179-aba9-9c59c39ddaa3

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (k : ℕ) :
    (4 * v ^ (2 * k) + (u * v) ^ k + u ^ (2 * k)) /
        (2 * (v ^ (2 * k) + (u * v) ^ k)) =
      (4 * ((v / u) ^ k) ^ 2 + (v / u) ^ k + 1) /
        (2 * (((v / u) ^ k) ^ 2 + (v / u) ^ k)) := by
  have hpowv : v ^ (2 * k) = (v ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  have hpowu : u ^ (2 * k) = (u ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  rw [hpowv, hpowu, mul_pow, div_pow]
  field_simp [hu.ne', hv.ne']
end FrontierMathLean
