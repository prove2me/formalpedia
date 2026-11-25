-- Prove2me | solution 1 for Erdos685Research.tendsto_log_nat_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:42:03.744449+00:00
-- url     : https://prove2.me/submissions/eeb47a08-cf4f-4160-bbb6-5c527c4313e0

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
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
end Erdos685Research
