-- Prove2me | solution 1 for ConservationLaws.perfectly_inelastic_collision_1d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:52:19.02742+00:00
-- url     : https://prove2.me/submissions/50eae0e9-e5ca-41bf-9f30-eebaee636af9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (mA mB uA uB w : ℝ) (hmA : 0 < mA) (hmB : 0 < mB)
    (hp : mA * uA + mB * uB = (mA + mB) * w) :
    w = (mA * uA + mB * uB) / (mA + mB) ∧
    ((1 / 2 : ℝ) * mA * uA ^ 2 + (1 / 2 : ℝ) * mB * uB ^ 2) -
      (1 / 2 : ℝ) * (mA + mB) * w ^ 2 =
      (1 / 2 : ℝ) * (mA * mB / (mA + mB)) * (uA - uB) ^ 2 := by
  have hmass : mA + mB ≠ 0 := ne_of_gt (add_pos hmA hmB)
  have hw : w = (mA * uA + mB * uB) / (mA + mB) := by
    apply (eq_div_iff hmass).2
    nlinarith [hp]
  constructor
  · exact hw
  · rw [hw]
    field_simp [hmass]
    ring
