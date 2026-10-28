-- Prove2me | solution 1 for CompositeLB.DetSC.ratio_eps_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:18:10.510986+00:00
-- url     : https://prove2.me/submissions/251b1840-9176-4523-a208-6dcd480be080

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

theorem solution (Q eps eps0 : ℝ) (hQ : 1 < Q)
    (heps : 0 < eps) (heps0 : 0 < eps0)
    (hlarge : 2 * Real.sqrt Q * eps ≤ eps0)
    (t : ℕ)
    (ht : t = Nat.floor ((Real.sqrt Q - 1) / 4 *
      Real.log (eps0 / (2 * Real.sqrt Q * eps)))) :
    1 / (2 * Real.sqrt Q) *
        Real.exp (-4 * (t : ℝ) / (Real.sqrt Q - 1)) ≥ eps / eps0 := by
  have hs : 1 < Real.sqrt Q := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hQ
  set s := Real.sqrt Q with hsdef
  have hs1 : 0 < s - 1 := by linarith
  have hden : 0 < 2 * s * eps := by positivity
  have hratio : 1 ≤ eps0 / (2 * s * eps) := by rw [le_div_iff₀ hden]; linarith
  have hratio0 : 0 < eps0 / (2 * s * eps) := by positivity
  set L := Real.log (eps0 / (2 * s * eps)) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hratio
  have htle : (t : ℝ) ≤ (s - 1) / 4 * L := by
    rw [ht]; exact Nat.floor_le (by positivity)
  have h4 : 4 * (t : ℝ) / (s - 1) ≤ L := by
    rw [div_le_iff₀ hs1]; nlinarith
  have hexp : Real.exp (-L) ≤ Real.exp (-4 * (t : ℝ) / (s - 1)) := by
    apply Real.exp_le_exp.mpr
    have : -4 * (t : ℝ) / (s - 1) = -(4 * (t : ℝ) / (s - 1)) := by ring
    rw [this]; linarith
  have hexpL : Real.exp (-L) = 2 * s * eps / eps0 := by
    rw [Real.exp_neg, hL, Real.exp_log hratio0, inv_div]
  rw [hexpL] at hexp
  have hpos : 0 < 1 / (2 * s) := by positivity
  have := mul_le_mul_of_nonneg_left hexp hpos.le
  have e : 1 / (2 * s) * (2 * s * eps / eps0) = eps / eps0 := by
    field_simp
  rw [e] at this
  exact this
