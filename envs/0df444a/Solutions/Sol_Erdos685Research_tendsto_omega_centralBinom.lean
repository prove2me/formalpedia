-- Prove2me | solution 1 for Erdos685Research.tendsto_omega_centralBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:54:30.018998+00:00
-- url     : https://prove2.me/submissions/532edb51-3bf6-4e56-966f-a1b68b73863f

module
public import Definitions.Def_Asymptotic_CentralGrowth
public import Definitions.Def_Asymptotic_PrimeCutoff
public import Definitions.Def_Asymptotic_LogCutoff
public import Definitions.Def_Erdos685ElementaryLowerBound_Solution
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_Asymptotic_CentralAsymptotic
public import Theorems.Thm_Erdos685Research_eventually_one_lt_cutoff
public import Theorems.Thm_Erdos685Research_tendsto_cutoff_add_one_mul_log_div
public import Theorems.Thm_Erdos685Research_tendsto_log_centralBinom_div
public import Theorems.Thm_Erdos685Research_tendsto_log_div_log_cutoff
public import Theorems.Thm_Erdos685Research_tendsto_log_div_log_two_mul
public import Theorems.Thm_Erdos685_choose_le_pow_omega
public import Theorems.Thm_Erdos685_primeFactors_card_le_cutoff


set_option autoImplicit false
@[expose] public section
public section
open Filter Real Finset
open scoped Topology ArithmeticFunction.omega
open Erdos685Research
namespace Erdos685Research
theorem _root_.solution :
    Tendsto (fun n : ℕ => (ω (Nat.centralBinom n) : ℝ) * Real.log n / (n : ℝ))
      atTop (𝓝 (Real.log 4)) := by
  have hlo : Tendsto (fun n : ℕ =>
      (Real.log (Nat.centralBinom n : ℝ) / (n : ℝ)) *
        (Real.log n / Real.log (2 * (n : ℝ)))) atTop (𝓝 (Real.log 4)) := by
    simpa using tendsto_log_centralBinom_div.mul tendsto_log_div_log_two_mul
  have hhi : Tendsto (fun n : ℕ =>
      (cutoff n + 1) * Real.log n / (n : ℝ) +
        (Real.log (Nat.centralBinom n : ℝ) / (n : ℝ)) *
          (Real.log n / Real.log (cutoff n))) atTop (𝓝 (Real.log 4)) := by
    simpa using tendsto_cutoff_add_one_mul_log_div.add
      (tendsto_log_centralBinom_div.mul tendsto_log_div_log_cutoff)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have h2pos : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
    have hbpos : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
    have hpow : (Nat.centralBinom n : ℝ) ≤
        (2 * (n : ℝ)) ^ (ω (Nat.centralBinom n)) := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact_mod_cast Erdos685.choose_le_pow_omega (by omega : 0 < 2 * n) (by omega : n ≤ 2 * n)
    have hlog := Real.log_le_log hbpos hpow
    rw [Real.log_pow] at hlog
    have hlow : Real.log (Nat.centralBinom n : ℝ) / Real.log (2 * (n : ℝ)) ≤
        (ω (Nat.centralBinom n) : ℝ) := (div_le_iff₀ h2pos).mpr hlog
    calc
      _ = (Real.log (Nat.centralBinom n : ℝ) / Real.log (2 * (n : ℝ))) *
          Real.log n / (n : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlow hlpos) hnpos.le
  · filter_upwards [eventually_ge_atTop 2, eventually_one_lt_cutoff] with n hn hcut
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hc : (Nat.centralBinom n).primeFactors.card = ω (Nat.centralBinom n) := by
      simp only [Nat.primeFactors, List.card_toFinset,
        ArithmeticFunction.cardDistinctFactors_apply]
    have hbound : (ω (Nat.centralBinom n) : ℝ) ≤ cutoff n + 1 +
        Real.log (Nat.centralBinom n : ℝ) / Real.log (cutoff n) := by
      simpa only [hc] using Erdos685.primeFactors_card_le_cutoff
        (Nat.centralBinom_pos n) hcut
    calc
      _ ≤ (cutoff n + 1 + Real.log (Nat.centralBinom n : ℝ) / Real.log (cutoff n)) *
          Real.log n / (n : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbound hlpos) hnpos.le
      _ = _ := by ring
end Erdos685Research
