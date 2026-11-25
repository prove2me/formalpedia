-- Prove2me | solution 1 for Erdos679.log_log_quotient_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:20:41.332315+00:00
-- url     : https://prove2.me/submissions/977d0d8b-ee86-46e8-be99-90b91bf47a6f

module
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos679_Gap

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution {x y : ℝ} (hx : exp (exp 1) < x) (hxy : x ≤ y) :
    log x / log (log x) ≤ log y / log (log y) := by
  have hxp : 0 < x := (Real.exp_pos _).trans hx
  have hlx : exp 1 < log x := (Real.lt_log_iff_exp_lt hxp).mpr hx
  have hlogs := Real.log_le_log hxp hxy
  have hanti := Real.log_div_self_antitoneOn hlx.le (hlx.le.trans hlogs) hlogs
  have he : (1 : ℝ) < exp 1 := by
    simp
  have hp : 0 < log (log y) / log y :=
    div_pos (Real.log_pos ((he.trans hlx).trans_le hlogs))
      ((Real.exp_pos 1).trans_le (hlx.le.trans hlogs))
  simpa only [one_div_div] using one_div_le_one_div_of_le hp hanti
end Erdos679
