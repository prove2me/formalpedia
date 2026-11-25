-- Prove2me | solution 1 for Erdos685Research.tendsto_cutoff_add_one_mul_log_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:46:40.709696+00:00
-- url     : https://prove2.me/submissions/3680e823-7dcf-49b3-8a45-1f1152337931

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Definitions.Def_Asymptotic_LogCutoff
public import Theorems.Thm_Erdos685Research_tendsto_log_nat_div_nat
public import Theorems.Thm_Erdos685Research_tendsto_log_nat

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos685Research
namespace Erdos685Research
theorem _root_.solution :
    Tendsto (fun n : ℕ => (cutoff n + 1) * Real.log n / (n : ℝ))
      atTop (𝓝 0) := by
  have h := (tendsto_log_nat.inv_tendsto_atTop).add tendsto_log_nat_div_nat
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  dsimp [cutoff]
  field_simp [hn0, hl0]
end Erdos685Research
