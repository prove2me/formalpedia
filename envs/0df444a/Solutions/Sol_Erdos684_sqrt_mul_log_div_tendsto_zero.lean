-- Prove2me | solution 1 for Erdos684.sqrt_mul_log_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:23.616822+00:00
-- url     : https://prove2.me/submissions/657269dc-5c2f-4a26-9686-d3c714a15f97

module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Analytic

set_option autoImplicit false
@[expose] public section
open Filter Real
open scoped Topology
public section
open Erdos684
namespace Erdos684
theorem _root_.solution :
    Tendsto (fun x : ℝ => 2 * sqrt x * log x / x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => log x / sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have he : (fun x : ℝ => 2 * sqrt x * log x / x) =ᶠ[atTop]
      (fun x => 2 * (log x / sqrt x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs : sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    have heq := congrArg (fun z : ℝ => z * log x) (Real.mul_self_sqrt hx.le)
    field_simp [hx.ne', hs]
    nlinarith
  simpa using (h.const_mul 2).congr' he.symm
end Erdos684
