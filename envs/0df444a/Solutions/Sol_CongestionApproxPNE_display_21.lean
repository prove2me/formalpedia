-- Prove2me | solution 1 for CongestionApproxPNE.display_21
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T15:09:01.157982+00:00
-- url     : https://prove2.me/submissions/b998c1ef-18a7-40f8-90c9-b51ddf41a9ab

import Mathlib

/-- Congestion games, display (21): `exp(xy/(x+y)) < (1 + x/y)^y < exp x` for `x, y > 0`. -/
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.exp (x * y / (x + y)) < (1 + x / y) ^ y ∧ (1 + x / y) ^ y < Real.exp x := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy0 : x + y ≠ 0 := by positivity
  have hbase : 0 < 1 + x / y := by positivity
  have hbne : (1 + x / y) ≠ 1 := by
    intro h
    have h' : x / y = 0 := by linarith
    exact (div_pos hx hy).ne' h'
  have hrw : (1 + x / y) ^ y = Real.exp (Real.log (1 + x / y) * y) := by
    rw [Real.rpow_def_of_pos hbase]
  have hinv : (1 + x / y)⁻¹ = y / (x + y) := by
    field_simp
    ring
  have hne : (1 + x / y)⁻¹ ≠ 1 := by
    rw [hinv]
    intro h
    rw [div_eq_iff hxy0] at h
    linarith
  have hlow : x / (x + y) < Real.log (1 + x / y) := by
    have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hbase) hne
    rw [Real.log_inv, hinv] at h
    have hid : 1 - y / (x + y) = x / (x + y) := by
      field_simp
      ring
    linarith
  constructor
  · rw [hrw]
    apply Real.exp_lt_exp.mpr
    have h := mul_lt_mul_of_pos_right hlow hy
    have h1 : (x / (x + y)) * y = x * y / (x + y) := by
      field_simp
    linarith
  · rw [hrw]
    apply Real.exp_lt_exp.mpr
    have hup' : Real.log (1 + x / y) < x / y := by
      have h := Real.log_lt_sub_one_of_pos hbase hbne
      have h1 : 1 + x / y - 1 = x / y := by ring
      linarith
    have h := mul_lt_mul_of_pos_right hup' hy
    have h1 : (x / y) * y = x := by
      field_simp
    linarith
