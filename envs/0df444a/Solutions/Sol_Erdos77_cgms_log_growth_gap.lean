-- Prove2me | solution 1 for Erdos77_cgms_log_growth_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:48:45.197697+00:00
-- url     : https://prove2.me/submissions/dd659fde-7210-469f-bfaa-8d408c7ad56c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_gnnw_diagonal_rate_37993

open Filter

theorem solution :
  Exists (fun a : Real =>
    And (0 < a) (And (a < 4)
      (Filter.Eventually (fun k : Nat =>
        Real.log (Erdos77.diagonalRamsey k) <= (k : Real) * Real.log a) Filter.atTop))) := by
  let c : Real := 3.7993
  have hc1 : 1 < c := by norm_num [c]
  have hc4 : c < 4 := by norm_num [c]
  have hcpos : 0 < c := by linarith
  have hlogc : 0 < Real.log c := Real.log_pos hc1
  have hlog4 : Real.log c < Real.log 4 := Real.log_lt_log hcpos hc4
  let eps : Real := (Real.log 4 / Real.log c - 1) / 2
  have heps : 0 < eps := by
    have hratio : 1 < Real.log 4 / Real.log c :=
      (lt_div_iff₀ hlogc).2 (by linarith)
    dsimp [eps]
    linarith
  have hscale : 1 + eps < Real.log 4 / Real.log c := by
    dsimp [eps]
    have hratio : 1 < Real.log 4 / Real.log c := (lt_div_iff₀ hlogc).2 (by linarith)
    linarith
  have hscaled : (1 + eps) * Real.log c < Real.log 4 := by
    rw [mul_comm (1 + eps) (Real.log c)]
    calc
      Real.log c * (1 + eps) < Real.log c * (Real.log 4 / Real.log c) :=
        mul_lt_mul_of_pos_left hscale hlogc
      _ = Real.log 4 := by field_simp
  have ha4 : c ^ (1 + eps) < 4 := by
    calc
      c ^ (1 + eps) = Real.exp (Real.log c * (1 + eps)) := Real.rpow_def_of_pos hcpos _
      _ < Real.exp (Real.log 4) := Real.exp_lt_exp.mpr (by nlinarith [hscaled])
      _ = 4 := Real.exp_log (by norm_num)
  have ha0 : 0 < c ^ (1 + eps) := Real.rpow_pos_of_pos hcpos _
  have ha1 : 1 < c ^ (1 + eps) := by
    have hpos : 0 < (1 + eps) * Real.log c := by positivity
    calc
      1 = Real.exp 0 := by simp
      _ < Real.exp (Real.log c * (1 + eps)) := Real.exp_lt_exp.mpr (by nlinarith [hpos])
      _ = c ^ (1 + eps) := (Real.rpow_def_of_pos hcpos _).symm
  refine ⟨c ^ (1 + eps), ha0, ha4, ?_⟩
  have hrate := Erdos77.gnnw_diagonal_rate_37993 eps heps
  filter_upwards [hrate, Filter.eventually_ge_atTop (1 : Nat)] with k hk hk1
  have hpow : c ^ ((1 + eps) * (k : Real)) = (c ^ (1 + eps)) ^ k := by
    calc
      c ^ ((1 + eps) * (k : Real)) = (c ^ (1 + eps)) ^ (k : Real) := by
        rw [← Real.rpow_mul (by positivity : 0 ≤ c)]
      _ = (c ^ (1 + eps)) ^ k := Real.rpow_natCast _ _
  by_cases hR : Erdos77.diagonalRamsey k = 0
  · rw [hR]
    simp only [Nat.cast_zero, Real.log_zero]
    have hkreal : (1 : Real) ≤ k := by exact_mod_cast hk1
    have hloga : 0 < Real.log (c ^ (1 + eps)) := Real.log_pos ha1
    positivity
  · have hRpos : 0 < (Erdos77.diagonalRamsey k : Real) := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mpr hR)
    have hlogbound : Real.log (Erdos77.diagonalRamsey k) ≤
        Real.log (c ^ ((1 + eps) * (k : Real))) :=
      Real.log_le_log hRpos (by exact_mod_cast hk)
    calc
      Real.log (Erdos77.diagonalRamsey k) ≤ Real.log (c ^ ((1 + eps) * (k : Real))) := hlogbound
      _ = (k : Real) * Real.log (c ^ (1 + eps)) := by
        rw [hpow, Real.log_pow]
