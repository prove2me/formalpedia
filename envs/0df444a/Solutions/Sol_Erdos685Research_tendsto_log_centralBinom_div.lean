-- Prove2me | solution 1 for Erdos685Research.tendsto_log_centralBinom_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:47:01.270322+00:00
-- url     : https://prove2.me/submissions/0a124de3-6476-4d59-91d2-158cd500c78a

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Asymptotic_CentralGrowth

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos685Research
namespace Erdos685Research
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (Nat.centralBinom n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 4)) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hnat
  have hlo : Tendsto (fun n : ℕ => Real.log 4 - Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 4)) := by
    simpa using tendsto_const_nhds.sub hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcb : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 4 ^ n)
      (show (4 : ℝ) ^ n ≤ (n : ℝ) * Nat.centralBinom n by
        exact_mod_cast (Nat.four_pow_lt_mul_centralBinom n hn).le)
    rw [Real.log_pow, Real.log_mul hnpos.ne' hcb.ne'] at h
    apply (le_div_iff₀ hnpos).mpr
    have heq : (Real.log 4 - Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) =
        (n : ℝ) * Real.log 4 - Real.log (n : ℝ) := by
      rw [sub_mul, div_mul_cancel₀ _ hnpos.ne']
      ring
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcb : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
    have h := Real.log_le_log hcb
      (show (Nat.centralBinom n : ℝ) ≤ (4 : ℝ) ^ n by
        exact_mod_cast Nat.centralBinom_le_four_pow n)
    rw [Real.log_pow] at h
    apply (div_le_iff₀ hnpos).mpr
    nlinarith
end Erdos685Research
