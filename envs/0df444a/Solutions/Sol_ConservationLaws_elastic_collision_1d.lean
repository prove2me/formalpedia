-- Prove2me | solution 1 for ConservationLaws.elastic_collision_1d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:52:24.121+00:00
-- url     : https://prove2.me/submissions/df8538e2-39e8-4fe4-988c-210203959472

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (mA mB uA uB vA vB : ℝ) (hmA : 0 < mA) (hmB : 0 < mB)
    (hp : mA * uA + mB * uB = mA * vA + mB * vB)
    (hE : (1 / 2 : ℝ) * mA * uA ^ 2 + (1 / 2 : ℝ) * mB * uB ^ 2 =
      (1 / 2 : ℝ) * mA * vA ^ 2 + (1 / 2 : ℝ) * mB * vB ^ 2) :
    (vA = uA ∧ vB = uB) ∨
    (vA = ((mA - mB) * uA + 2 * mB * uB) / (mA + mB) ∧
     vB = (2 * mA * uA + (mB - mA) * uB) / (mA + mB)) := by
  have hmass : mA + mB ≠ 0 := ne_of_gt (add_pos hmA hmB)
  have hpm : mA * (vA - uA) + mB * (vB - uB) = 0 := by
    linarith [hp]
  have hem : mA * (vA - uA) * (vA + uA) +
      mB * (vB - uB) * (vB + uB) = 0 := by
    nlinarith [hE]
  have hf : (vA - uA) * (vA + uA - vB - uB) = 0 := by
    have h : mA * ((vA - uA) * (vA + uA - vB - uB)) = 0 := by
      calc
        _ = (mA * (vA - uA) * (vA + uA) +
            mB * (vB - uB) * (vB + uB)) -
            (vB + uB) * (mA * (vA - uA) + mB * (vB - uB)) := by ring
        _ = 0 := by rw [hem, hpm]; ring
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hmA)
  rcases mul_eq_zero.mp hf with hsame | hrelative
  · left
    have ha : vA = uA := sub_eq_zero.mp hsame
    constructor
    · exact ha
    · rw [ha] at hp
      have hb : mB * (vB - uB) = 0 := by nlinarith [hp]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left (ne_of_gt hmB))
  · right
    have hrel : vA + uA = vB + uB := by linarith
    have hbm := congrArg (fun z : ℝ => mB * z) hrel
    have ham := congrArg (fun z : ℝ => mA * z) hrel
    constructor
    · apply (eq_div_iff hmass).2
      nlinarith [hp, hbm]
    · apply (eq_div_iff hmass).2
      nlinarith [hp, ham]
