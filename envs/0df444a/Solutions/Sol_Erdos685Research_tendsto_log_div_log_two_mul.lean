-- Prove2me | solution 1 for Erdos685Research.tendsto_log_div_log_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:46:09.501354+00:00
-- url     : https://prove2.me/submissions/1eb34a8a-5500-4faf-ad6d-68e7bdaa4bc8

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Definitions.Def_Asymptotic_LogCutoff
public import Theorems.Thm_Erdos685Research_tendsto_log_nat

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos685Research
namespace Erdos685Research
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log n / Real.log (2 * (n : ℝ))) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun n : ℕ => Real.log 2 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_nat
  have hbase : Tendsto (fun n : ℕ => Real.log 2 / Real.log n + 1)
      atTop (𝓝 (1 : ℝ)) := by simpa using hsmall.add tendsto_const_nhds
  have h := hbase.inv₀ (by norm_num)
  simp only [inv_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne']
  have heq : Real.log 2 / Real.log n + 1 =
      (Real.log 2 + Real.log n) / Real.log n := by
    field_simp [hlpos.ne']
  rw [heq, inv_div]
end Erdos685Research
