-- Prove2me | solution 2 for AvramDividend.Classical.positive_midpoint_multiplicative_of_ratio_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:24:08.573903+00:00
-- url     : https://prove2.me/submissions/b57b3651-d87a-4c25-bcd1-71e994400b9a

import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Ordered forward ratios force positive midpoint multiplicative concavity. -/
theorem solution
    (f : ℝ → ℝ)
    (hfpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hratio : ∀ x y t : ℝ, 0 < x → x ≤ y → 0 < t →
      f x / f (x + t) ≤ f y / f (y + t)) :
    ∀ x y : ℝ, 0 < x → x < y →
      f x * f y ≤ (f ((x + y) / 2)) ^ 2 := by
  intro x y hx hxy
  let m : ℝ := (x + y) / 2
  have hxm : x ≤ m := by
    dsimp [m]
    linarith
  have hmy : m ≤ y := by
    dsimp [m]
    linarith
  have hmpos : 0 < m := lt_of_lt_of_le hx hxm
  have hstep : 0 < m - x := by
    dsimp [m]
    linarith
  have hxm_eq : x + (m - x) = m := by ring
  have hmy_eq : m + (m - x) = y := by
    dsimp [m]
    ring
  have hratio' := hratio x m (m - x) hx hxm hstep
  rw [hxm_eq, hmy_eq] at hratio'
  have hden1 : 0 < f m := hfpos m hmpos
  have hden2 : 0 < f y := hfpos y (lt_of_lt_of_le hmpos hmy)
  have hmul : f x * f y ≤ f m * f m :=
    (div_le_div_iff₀ hden1 hden2).mp hratio'
  simpa [m, pow_two] using hmul
