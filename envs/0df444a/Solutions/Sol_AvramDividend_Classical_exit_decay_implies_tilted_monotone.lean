-- Prove2me | solution 1 for AvramDividend.Classical.exit_decay_implies_tilted_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T14:18:53.458003+00:00
-- url     : https://prove2.me/submissions/0c4a64a2-cbf8-453b-b2bd-bf3acc54cdad

import Mathlib

open Set

theorem solution (W : ℝ → ℝ) (φ : ℝ)
    (hbound : ∀ x y : ℝ, 0 < x → x ≤ y →
       W x ≤ Real.exp (-φ * (y - x)) * W y) :
    MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  intro x hx y hy hxy
  have hb := hbound x y hx hxy
  calc
    Real.exp (-φ * x) * W x ≤
        Real.exp (-φ * x) * (Real.exp (-φ * (y - x)) * W y) :=
      mul_le_mul_of_nonneg_left hb (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-φ * y) * W y := by
      have heq : -φ * x + (-φ * (y - x)) = -φ * y := by ring
      rw [← mul_assoc, ← Real.exp_add, heq]
