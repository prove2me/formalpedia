-- Prove2me | solution 1 for Erdos679.eventually_nth_prime_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:41:34.927833+00:00
-- url     : https://prove2.me/submissions/bde9af20-d376-49bf-8e6a-9505125e7c6a

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
public import Theorems.Thm_Erdos679_chebyshev_lower_ratio

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤
      (3 / 2 : ℝ) * n * log n := by
  have hlim := (chebyshev_lower_ratio (3 / 2) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hconstant : (1 : ℝ) < (3 / 2) * log 2 := by
    have hlog := Real.lt_log_one_add_of_pos (x := 1) (by norm_num)
    norm_num at hlog
    linarith
  have hbound := hlim.eventually (lt_mem_nhds hconstant)
  have hx : Tendsto (fun n : ℕ => (3 / 2 : ℝ) * n * log n) atTop atTop := by
    have h := tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [mul_assoc, Function.comp_apply] using h.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 2)
  filter_upwards [hbound, hx.eventually_gt_atTop 1, eventually_gt_atTop (0 : ℕ)]
    with n hn hxn hn0
  have hpi := Chebyshev.pi_ge' hxn
  have hcount : n < Nat.primeCounting ⌊(3 / 2 : ℝ) * n * log n⌋₊ := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt := (lt_div_iff₀ hnpos).mp hn
    have hreal : (n : ℝ) < Nat.primeCounting ⌊(3 / 2 : ℝ) * n * log n⌋₊ := by
      linarith
    exact_mod_cast hreal
  change n < Nat.count Nat.Prime (⌊(3 / 2 : ℝ) * n * log n⌋₊ + 1) at hcount
  have hp := (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp hcount
  change Nat.nth Nat.Prime n < ⌊(3 / 2 : ℝ) * n * log n⌋₊ + 1 at hp
  have hpn : Nat.nth Nat.Prime n ≤ ⌊(3 / 2 : ℝ) * n * log n⌋₊ := Nat.lt_succ_iff.mp hp
  exact (show (Nat.nth Nat.Prime n : ℝ) ≤ ⌊(3 / 2 : ℝ) * n * log n⌋₊ by
    exact_mod_cast hpn).trans (Nat.floor_le (by linarith))
end Erdos679
