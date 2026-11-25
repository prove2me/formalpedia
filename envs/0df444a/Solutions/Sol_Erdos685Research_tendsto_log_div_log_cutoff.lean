-- Prove2me | solution 1 for Erdos685Research.tendsto_log_div_log_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:50:26.696277+00:00
-- url     : https://prove2.me/submissions/da3c17ae-845a-4500-bcfc-5e90ddd199af

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Definitions.Def_Asymptotic_LogCutoff
public import Theorems.Thm_Erdos685Research_tendsto_loglog_div_log

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos685Research
namespace Erdos685Research
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log n / Real.log (cutoff n)) atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => 1 - 2 *
      (Real.log (Real.log n) / Real.log n)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_loglog_div_log)
  have h := hbase.inv₀ (by norm_num)
  simp only [inv_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [cutoff, Real.log_div hnpos.ne' (pow_ne_zero 2 hlpos.ne'), Real.log_pow]
  have heq : 1 - 2 * (Real.log (Real.log n) / Real.log n) =
      (Real.log n - 2 * Real.log (Real.log n)) / Real.log n := by
    field_simp [hlpos.ne']
  rw [heq, inv_div]
  norm_num
end Erdos685Research
