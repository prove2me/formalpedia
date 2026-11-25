-- Prove2me | solution 1 for Erdos685Research.eventually_one_lt_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:41:57.794972+00:00
-- url     : https://prove2.me/submissions/0a18ab62-5285-43df-bdc3-fb3f682b727e

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Definitions.Def_Asymptotic_LogCutoff

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos685Research
namespace Erdos685Research
theorem _root_.solution : ∀ᶠ n : ℕ in atTop, 1 < cutoff n := by
  have h : Tendsto (fun n : ℕ => Real.log n ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  dsimp [cutoff]
  rw [one_lt_div (sq_pos_of_pos hlpos)]
  exact (div_lt_one hnpos).mp hn
end Erdos685Research
