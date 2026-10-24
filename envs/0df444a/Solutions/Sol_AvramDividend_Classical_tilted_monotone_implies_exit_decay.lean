-- Prove2me | solution 1 for AvramDividend.Classical.tilted_monotone_implies_exit_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:58:23.728998+00:00
-- url     : https://prove2.me/submissions/f7353795-ad4c-4e8f-ab77-c39042487538

import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-!
The converse elementary normalisation bridge: monotonicity of the
Esscher-tilted function implies the exponential scale comparison.
-/
theorem solution (W : ℝ → ℝ) (φ : ℝ)
    (htilt : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
  intro x y hx hxy
  have hmono : Real.exp (-φ * x) * W x ≤
      Real.exp (-φ * y) * W y :=
    htilt hx (lt_of_lt_of_le hx hxy) hxy
  have hidentity : W x = Real.exp (φ * x) *
      (Real.exp (-φ * x) * W x) := by
    rw [← mul_assoc, ← Real.exp_add]
    simp [neg_mul]
  calc
    W x = Real.exp (φ * x) * (Real.exp (-φ * x) * W x) :=
      hidentity
    _ ≤ Real.exp (φ * x) * (Real.exp (-φ * y) * W y) :=
      mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    _ = Real.exp (-φ * (y - x)) * W y := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring
