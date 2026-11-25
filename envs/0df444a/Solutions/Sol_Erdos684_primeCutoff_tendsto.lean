-- Prove2me | solution 1 for Erdos684.primeCutoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:30.104643+00:00
-- url     : https://prove2.me/submissions/fcb1b00e-a4de-4ab8-bf5a-75b25167f9ba

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
    Tendsto (fun n : ℕ => (primeCutoff n : ℝ)) atTop atTop := by
  have hL : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun n : ℕ => 256 * (log (n : ℝ)) ^ 2) atTop atTop := by
    simpa only [pow_two] using
      (hL.atTop_mul_atTop₀ hL).const_mul_atTop (by norm_num : (0 : ℝ) < 256)
  exact tendsto_atTop_mono (fun n => Nat.le_ceil _) hbase
end Erdos684
