-- Prove2me | solution 1 for CosmologyEOS.acceleration_iff_w_lt_neg_third
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:10:27.145009+00:00
-- url     : https://prove2.me/submissions/f204eb48-00fd-4c06-8994-097cb24f1f03

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

theorem solution (G w : ℝ) (hG : 0 < G) (a ε p : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hε : 0 < ε t) (heos : p t = w * ε t)
    (hacc : AccelerationEquation G 0 a ε p t) :
    0 < deriv (deriv a) t ↔ w < -1 / 3 := by
  unfold AccelerationEquation at hacc
  rw [heos] at hacc
  have key : deriv (deriv a) t = a t * (-(4 * π * G * ε t) * (1 + 3 * w) / 3) := by
    field_simp at hacc ⊢; linarith
  have hk : 0 < 4 * π * G * ε t := by positivity
  rw [key]
  constructor
  · intro h
    have h2 : 0 < -(4 * π * G * ε t) * (1 + 3 * w) / 3 := (pos_iff_pos_of_mul_pos h).1 ha |>.trans_le le_rfl
    by_contra hw
    rw [not_lt] at hw
    have : 0 ≤ 1 + 3 * w := by linarith
    nlinarith
  · intro hw
    apply mul_pos ha
    have : 1 + 3 * w < 0 := by linarith
    nlinarith
