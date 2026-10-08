-- Prove2me | solution 1 for BarvinokCount.ShortFormula.two_pow_iterCount_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:25:49.160708+00:00
-- url     : https://prove2.me/submissions/d2a7c033-01a9-4cd0-9f48-205cb5887827

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_iterCount

open BarvinokCount.ShortFormula in
theorem solution {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    (((2 : ℝ) ^ d) ^ iterCount d N) ≤
      Real.exp (((-Real.log (Real.log (1.9 : ℝ))) / (Real.log (d : ℝ) - Real.log ((d : ℝ) - 1)) + 1) *
          Real.log ((2 : ℝ) ^ d)) *
        (Real.log (N : ℝ)) ^
          (Real.log ((2 : ℝ) ^ d) / (Real.log (d : ℝ) - Real.log ((d : ℝ) - 1))) := by
  set D := Real.log (d : ℝ) - Real.log ((d : ℝ) - 1) with hDdef
  set L := Real.log ((2 : ℝ) ^ d) with hLdef
  have hd1 : (1 : ℝ) < (d : ℝ) - 1 + 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hD : 0 < D := by
    rw [hDdef, sub_pos]
    exact Real.log_lt_log hdpos (by linarith)
  have hL : 0 < L := by
    rw [hLdef]; apply Real.log_pos
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log (1.9 : ℝ) < Real.log (N : ℝ) :=
    Real.log_lt_log (by norm_num) (by linarith)
  have hl19 : 0 < Real.log (1.9 : ℝ) := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log (N : ℝ) := by linarith
  have hll : Real.log (Real.log (1.9 : ℝ)) < Real.log (Real.log (N : ℝ)) :=
    Real.log_lt_log hl19 hlogN
  set x := (-Real.log (Real.log (1.9 : ℝ)) + Real.log (Real.log (N : ℝ))) / D with hxdef
  have hx : 0 ≤ x := by
    rw [hxdef]; apply div_nonneg _ hD.le; linarith
  have hT : iterCount d N = ⌈x⌉₊ := by
    unfold iterCount
    rw [if_neg (by omega)]
  have hceil : ((⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le
  have h2d : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  rw [hT]
  have hlhs : ((2 : ℝ) ^ d) ^ ⌈x⌉₊ = Real.exp (((⌈x⌉₊ : ℕ) : ℝ) * L) := by
    rw [hLdef, ← Real.rpow_natCast, Real.rpow_def_of_pos h2d, mul_comm]
  have hrhs : (Real.log (N : ℝ)) ^ (L / D) = Real.exp (Real.log (Real.log (N : ℝ)) * (L / D)) := by
    rw [Real.rpow_def_of_pos hlogNpos]
  rw [hlhs, hrhs, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have : (x + 1) * L = (-Real.log (Real.log 1.9) / D + 1) * L + Real.log (Real.log ↑N) * (L / D) := by
    rw [hxdef]; field_simp; ring
  rw [← this]
  exact mul_le_mul_of_nonneg_right hceil hL.le
