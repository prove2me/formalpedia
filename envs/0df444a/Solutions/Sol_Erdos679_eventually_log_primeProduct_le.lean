-- Prove2me | solution 1 for Erdos679.eventually_log_primeProduct_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:50:20.6083+00:00
-- url     : https://prove2.me/submissions/d3fb9250-437e-46d2-b232-6fec1ef7ace6

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
public import Theorems.Thm_Erdos679_eventually_nth_prime_le
public import Theorems.Thm_Erdos679_log_primeProduct_le_sum
public import Theorems.Thm_Erdos679_eventually_log_factorial_le


set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution :
    ∀ᶠ m : ℕ in atTop, log (primeProduct m : ℝ) ≤
      m * (log m + log (log m) - (3 / 10 : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_nth_prime_le
  let L := max N 2
  have hL : 2 ≤ L := le_max_right _ _
  have hp : ∀ i ≥ L, (Nat.nth Nat.Prime i : ℝ) ≤ (3 / 2 : ℝ) * i * log i :=
    fun i hi => hN i ((le_max_left _ _).trans hi)
  have hpref : Tendsto (fun m : ℕ => log (primeProduct L : ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall := hpref.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 10)
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop L, eventually_log_factorial_le,
    hsmall, hlogtop.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ)]
    with m hm hfact hsmall hlog hm0
  have hbound := log_primeProduct_le_sum L hL hp hm hlog
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hprefix := (div_lt_iff₀ hmpos).mp hsmall
  have hconstant := Real.log_le_sub_one_of_pos (x := (3 / 2 : ℝ)) (by norm_num)
  have hcm := mul_le_mul_of_nonneg_left hconstant hmpos.le
  nlinarith
end Erdos679
