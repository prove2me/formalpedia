-- Prove2me | solution 1 for Erdos679.log_mul_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:20:24.731483+00:00
-- url     : https://prove2.me/submissions/daeb1a45-79a9-4381-8691-e308c93bf8c0

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

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => log (a * x * log x) / log x) atTop (𝓝 1) := by
  have hc : Tendsto (fun x : ℝ => log a / log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hl : Tendsto (fun x : ℝ => log (log x) / log x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hs := (hc.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))).add hl
  have he : (fun x : ℝ => log (a * x * log x) / log x) =ᶠ[atTop]
      (fun x => log a / log x + 1 + log (log x) / log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.log_mul (mul_ne_zero ha.ne' (by positivity)) (Real.log_pos hx).ne',
      Real.log_mul ha.ne' (by positivity)]
    field_simp [(Real.log_pos hx).ne']
  simpa using hs.congr' he.symm
end Erdos679
