-- Prove2me | solution 1 for AvramDividend.Classical.quadratic_exponent_limit_nat_multiples_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:54:26.579378+00:00
-- url     : https://prove2.me/submissions/79382ae2-83ee-4a2b-be05-ad9614a424c1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter
open scoped Topology

theorem solution (f : ℝ → ℝ) (a : ℝ)
    (hf : Tendsto (fun n : ℕ =>
      f ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2))
      atTop (nhds a))
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ =>
      f ((m : ℝ) * ((n : ℝ) + 1)) /
        (((m : ℝ) * ((n : ℝ) + 1)) ^ 2))
      atTop (nhds a) := by
  let i : ℕ → ℕ := fun n => m * n + (m - 1)
  have hm1 : 1 ≤ m := hm
  have hmon (n : ℕ) : n ≤ i n := by
    dsimp [i]
    have hprod : 1 * n ≤ m * n :=
      Nat.mul_le_mul_right n hm1
    omega
  have hi : Tendsto i atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    exact le_trans hn (hmon n)
  have hni (n : ℕ) : i n + 1 = m * (n + 1) := by
    dsimp [i]
    calc
      m * n + (m - 1) + 1 = m * n + m := by omega
      _ = m * (n + 1) := by ring
  have hcast (n : ℕ) :
      ((i n : ℕ) : ℝ) + 1 = (m : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast hni n
  have hcomp := hf.comp hi
  change Tendsto (fun n : ℕ =>
    f (((i n : ℕ) : ℝ) + 1) /
      ((((i n : ℕ) : ℝ) + 1) ^ 2)) atTop (nhds a) at hcomp
  have hEq :
      (fun n : ℕ =>
        f (((i n : ℕ) : ℝ) + 1) /
          ((((i n : ℕ) : ℝ) + 1) ^ 2)) =
      (fun n : ℕ =>
        f ((m : ℝ) * ((n : ℝ) + 1)) /
          (((m : ℝ) * ((n : ℝ) + 1)) ^ 2)) := by
    funext n
    rw [hcast n]
  rw [hEq] at hcomp
  exact hcomp
