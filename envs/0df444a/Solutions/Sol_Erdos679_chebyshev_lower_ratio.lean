-- Prove2me | solution 1 for Erdos679.chebyshev_lower_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:47.254958+00:00
-- url     : https://prove2.me/submissions/bb446ad6-8d7e-4deb-924d-0c7b832ef93c

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
public import Theorems.Thm_Erdos679_log_add_div_tendsto_zero
public import Theorems.Thm_Erdos679_log_mul_log_ratio

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      (((a * x * log x - 1) * log 2 - log (a * x * log x + 2)) /
        log (a * x * log x)) / x) atTop (𝓝 (a * log 2)) := by
  have hx : Tendsto (fun x : ℝ => x * log x) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hax : Tendsto (fun x : ℝ => a * x * log x) atTop atTop := by
    simpa only [mul_assoc] using hx.const_mul_atTop ha
  have hi : Tendsto (fun x : ℝ => 1 / (x * log x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx
  have hl : Tendsto (fun x : ℝ => log (a * x * log x + 2) / (x * log x))
      atTop (𝓝 0) := by
    have h := ((log_add_div_tendsto_zero 2).comp hax).mul_const a
    convert h using 1 <;> try simp
    ext x
    field_simp
  have hn := (((tendsto_const_nhds :
    Tendsto (fun _ : ℝ => a) atTop (𝓝 a)).sub hi).mul_const (log 2)).sub hl
  have hden := log_mul_log_ratio a ha
  have hquot := hn.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have he : (fun x : ℝ =>
      (((a * x * log x - 1) * log 2 - log (a * x * log x + 2)) /
        log (a * x * log x)) / x) =ᶠ[atTop]
      (fun x => (((a - 1 / (x * log x)) * log 2 -
        log (a * x * log x + 2) / (x * log x)) /
          (log (a * x * log x) / log x))) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hax.eventually_gt_atTop 1] with x hx hax1
    have hx0 : x ≠ 0 := by positivity
    have hl0 : log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp [hx0, hl0, (Real.log_pos hax1).ne']
  simpa using hquot.congr' he.symm
end Erdos679
