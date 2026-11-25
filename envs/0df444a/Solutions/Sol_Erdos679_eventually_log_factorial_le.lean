-- Prove2me | solution 1 for Erdos679.eventually_log_factorial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:40.779889+00:00
-- url     : https://prove2.me/submissions/dae9a2cb-15f1-4967-a2e4-e937e059bcd4

module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_StirlingBound
public import Theorems.Thm_Erdos679_log_factorial_le_stirling

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop,
      log (n.factorial : ℝ) ≤ (n : ℝ) * log n - (9 / 10 : ℝ) * n := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := hone.add (hlog.div_const 2)
  have hsmall := hsum.eventually_lt_const (by norm_num : (0 : ℝ) + 0 / 2 < 1 / 10)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hratio : (1 + log (n : ℝ) / 2) / (n : ℝ) < 1 / 10 := by
    change (1 : ℝ) / (n : ℝ) + (log (n : ℝ) / (n : ℝ)) / 2 < 1 / 10 at hsmall
    calc
      (1 + log (n : ℝ) / 2) / (n : ℝ) =
          1 / (n : ℝ) + (log (n : ℝ) / (n : ℝ)) / 2 := by ring
      _ < 1 / 10 := hsmall
  have hlinear := (div_lt_iff₀ hnpos).mp hratio
  have hbound := log_factorial_le_stirling n hn
  linarith
end Erdos679
