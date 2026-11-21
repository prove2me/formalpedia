-- Prove2me | solution 1 for Champernowne.tendsto_err_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:42.357297+00:00
-- url     : https://prove2.me/submissions/f90d857d-708d-4989-a83c-c20275548be5

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_champM_pos
public import Theorems.Thm_Champernowne_tendsto_champM_atTop
public import Theorems.Thm_P2M_Champernowne_err_mul_le_pow__c0fdad917eb6

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (w : List ℕ) :
    Tendsto (fun n => (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) / n)
      atTop (𝓝 0) := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) - 1 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hden : Tendsto (fun n => ((b : ℝ) - 1) * (champM b n : ℝ))
      atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by linarith)).mpr
      (tendsto_natCast_atTop_atTop.comp (tendsto_champM_atTop hb))
  have hg : Tendsto (fun n =>
      (2 * (7 * ((w.length : ℝ) + 1) * (b : ℝ) ^ (2 * w.length) * (b : ℝ) ^ 2))
      / (((b : ℝ) - 1) * (champM b n : ℝ))) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h0 : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  · filter_upwards [(tendsto_champM_atTop hb).eventually_ge_atTop 2,
      Filter.eventually_ge_atTop 1] with n hM2 hn1
    have h0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hM0 : (0 : ℝ) < ((b : ℝ) - 1) * (champM b n : ℝ) := by
      have hMpos : (0 : ℝ) < (champM b n : ℝ) := by
        exact_mod_cast champM_pos b n
      nlinarith
    rw [div_le_div_iff₀ h0 hM0]
    have := err_mul_le_pow' hb n w hM2
    have hcast2 : ((7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * ((b - 1) * champM b n) : ℕ) : ℝ)
        = (7 * ((w.length : ℝ) + 1) * (b : ℝ) ^ (2 * w.length) * (b : ℝ) ^ champM b n)
          * (((b : ℝ) - 1) * (champM b n : ℝ)) := by
      have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      push_cast [hb1]
      ring
    have hcast3 : ((2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n : ℕ) : ℝ)
        = 2 * (7 * ((w.length : ℝ) + 1) * (b : ℝ) ^ (2 * w.length) * (b : ℝ) ^ 2) * n := by
      push_cast; ring
    rw [← hcast2, ← hcast3]
    exact_mod_cast this
end Champernowne
