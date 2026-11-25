-- Prove2me | solution 1 for Erdos684.eventually_upper_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:03:29.421677+00:00
-- url     : https://prove2.me/submissions/e50bdfd2-94bd-42a8-8b0c-8b2061dca3bb

module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Analytic
public import Theorems.Thm_Erdos684_eventually_theta_ge_half
public import Theorems.Thm_Erdos684_primeCutoff_tendsto

set_option autoImplicit false
@[expose] public section
open Filter Real
open scoped Topology
public section
open Erdos684
namespace Erdos684
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ log (n : ℝ) ∧
      0 < n ∧
      2 * primeCutoff n ≤ n ∧
      windowLength n ≤ n ∧
      32 * log (n : ℝ) ≤ (windowLength n : ℝ) ∧
      (windowLength n : ℝ) ≤ 33 * log (n : ℝ) ∧
      256 * (log (n : ℝ)) ^ 2 ≤ (primeCutoff n : ℝ) ∧
      (primeCutoff n : ℝ) ≤ 257 * (log (n : ℝ)) ^ 2 ∧
      log ((n + windowLength n : ℕ) : ℝ) ≤ 2 * log (n : ℝ) ∧
      (primeCutoff n : ℝ) / 2 ≤ Chebyshev.theta (primeCutoff n) ∧
      (2 * primeCutoff n : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 := by
  have hL : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (log (n : ℝ)) ^ 2 / n) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hxr : Tendsto (fun n : ℕ => 2 * (256 * (log (n : ℝ)) ^ 2 + 1) / n)
      atTop (𝓝 0) := by
    convert ((hratio.const_mul 512).add (hone.const_mul 2)) using 1 <;> try norm_num
    ext n
    ring
  have hlr : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have har : Tendsto (fun n : ℕ => 33 * log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hlr.const_mul 33
  have hxsmall := hxr.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hasmall := har.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have htheta := primeCutoff_tendsto.eventually eventually_theta_ge_half
  filter_upwards [hL.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ),
    hxsmall, hasmall, htheta] with n hL1 hn0 hxs has ht
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL0 : 0 ≤ log (n : ℝ) := by linarith
  have hLsq : 1 ≤ (log (n : ℝ)) ^ 2 := by nlinarith
  have hAlower : 32 * log (n : ℝ) ≤ (windowLength n : ℝ) := Nat.le_ceil _
  have hAceil : (windowLength n : ℝ) < 32 * log (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hAupper : (windowLength n : ℝ) ≤ 33 * log (n : ℝ) := by linarith
  have hXlower : 256 * (log (n : ℝ)) ^ 2 ≤ (primeCutoff n : ℝ) := Nat.le_ceil _
  have hXceil : (primeCutoff n : ℝ) < 256 * (log (n : ℝ)) ^ 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hXupper : (primeCutoff n : ℝ) ≤ 257 * (log (n : ℝ)) ^ 2 := by linarith
  have hxlarge := (div_lt_iff₀ hnpos).mp hxs
  have halarge := (div_lt_iff₀ hnpos).mp has
  have h2X : 2 * primeCutoff n ≤ n := by
    have h : (2 : ℝ) * primeCutoff n ≤ n := by linarith
    exact_mod_cast h
  have hAn : windowLength n ≤ n := by
    have h : (windowLength n : ℝ) ≤ n := by linarith
    exact_mod_cast h
  have hsumpos : (0 : ℝ) < ((n + windowLength n : ℕ) : ℝ) := by positivity
  have hsum : ((n + windowLength n : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : n + windowLength n ≤ 2 * n)
  have hlogsum := Real.log_le_log hsumpos hsum
  rw [Real.log_mul (by norm_num) hnpos.ne'] at hlogsum
  have hlogtwo := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
  have hlogbound : log ((n + windowLength n : ℕ) : ℝ) ≤ 2 * log (n : ℝ) := by linarith
  refine ⟨hL1, hn0, h2X, hAn, hAlower, hAupper, hXlower, hXupper, hlogbound, ht, ?_⟩
  nlinarith
end Erdos684
