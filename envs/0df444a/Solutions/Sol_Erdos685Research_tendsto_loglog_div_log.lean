-- Prove2me | solution 1 for Erdos685Research.tendsto_loglog_div_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:46:07.181227+00:00
-- url     : https://prove2.me/submissions/ea418851-cda1-49c9-a29d-7bab9493b45a

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Definitions.Def_Asymptotic_LogCutoff
public import Theorems.Thm_Erdos685Research_tendsto_log_nat

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos685Research
namespace Erdos685Research
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_log_nat
end Erdos685Research
