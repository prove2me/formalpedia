-- Prove2me | solution 1 for Erdos684.eventually_theta_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:56:44.910713+00:00
-- url     : https://prove2.me/submissions/76100e19-642f-4d0c-b730-1c67176bade0

module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Analytic
public import Theorems.Thm_Erdos684_log_add_div_tendsto_zero
public import Theorems.Thm_Erdos684_sqrt_mul_log_div_tendsto_zero

set_option autoImplicit false
@[expose] public section
open Filter Real
open scoped Topology
public section
open Erdos684
namespace Erdos684
theorem _root_.solution :
    ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.theta x := by
  have hconst : Tendsto (fun x : ℝ => log 2 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have herr : Tendsto (fun x : ℝ => log 2 / x + log (x + 2) / x +
      2 * sqrt x * log x / x) atTop (𝓝 0) := by
    simpa only [add_zero] using
      (hconst.add (log_add_div_tendsto_zero 2)).add sqrt_mul_log_div_tendsto_zero
  have hlogtwo : (1 / 2 : ℝ) < log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := 1) (by norm_num)
    norm_num at h
    linarith
  have hsmall := herr.eventually_lt_const (by linarith : (0 : ℝ) < log 2 - 1 / 2)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hratio : (log 2 + log (x + 2) + 2 * sqrt x * log x) / x < log 2 - 1 / 2 := by
    simpa only [add_div] using hx
  have hb := (div_lt_iff₀ hx0).mp hratio
  have ht := Chebyshev.theta_ge' hx1
  nlinarith
end Erdos684
