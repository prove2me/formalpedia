-- Prove2me | solution 1 for GJKKL.Main.Regime.union_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:45.089785+00:00
-- url     : https://prove2.me/submissions/478967d3-68f7-4f87-b758-07fc317d61e0

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_E_le_d
public import Theorems.Thm_GJKKL_Main_Regime_E_pos
public import Theorems.Thm_GJKKL_Main_Regime_E_sq
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_freedman_exp
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_k_pos
public import Theorems.Thm_GJKKL_Main_Regime_one_le_dcube
public import Theorems.Thm_GJKKL_Main_Regime_rp_pos
public import Theorems.Thm_GJKKL_TrackHyp_k_pos


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
set_option maxHeartbeats 800000
namespace GJKKL.Main.Regime
theorem _root_.solution {n T : ℕ} (hT : T ≤ n) (hn : (n : ℝ) ≤ Real.exp (d ^ (ε ^ 3))) :
    (T : ℝ) * (2 * n) * Real.exp (-((d ^ (1 - ε / 8) / 2) ^ 2 /
      (2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (d ^ (1 - ε / 8) / 2 + 5 * k * d)))) ≤ 1 / 2 := by
  have hfe := R.freedman_exp
  have hsq := R.E_sq
  have hE := R.E_pos
  have hEd := R.E_le_d
  have hk := R.k_ge
  have hQ1 := R.one_le_dcube
  have hdε := R.rp_pos (1 - ε)
  set E := d ^ (1 - ε / 8) with hE_def
  set Q := d ^ (ε ^ 3) with hQ
  have hden : 0 < 2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (E / 2 + 5 * k * d) := by
    have h5 : 0 < 5 * (k : ℝ) * d := mul_pos (mul_pos (by norm_num) R.k_pos) R.d_pos
    exact mul_pos (mul_pos two_pos (mul_pos (mul_pos (by norm_num) (pow_pos R.k_pos 3)) hdε))
      (by linarith)
  -- the exponent is at least `2Q + 2`
  have hratio : 2 * Q + 2 ≤ (E / 2) ^ 2 /
      (2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (E / 2 + 5 * k * d)) := by
    rw [le_div_iff₀ hden]
    have hs : E / 2 + 5 * k * d ≤ 6 * k * d := by nlinarith [R.d_pos]
    have hk3 : 0 ≤ 200 * (k : ℝ) ^ 3 * d ^ (1 - ε) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg R.k_pos.le 3)) hdε.le
    have h1 : 2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (E / 2 + 5 * k * d) ≤
        1200 * (k : ℝ) ^ 4 * d ^ (1 - ε) * d := by
      have := mul_le_mul_of_nonneg_left hs hk3
      linarith
    have h2 : 2 * Q + 2 ≤ 4 * Q := by linarith
    have h3 : (2 * Q + 2) * (2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (E / 2 + 5 * k * d)) ≤
        4 * Q * (1200 * (k : ℝ) ^ 4 * d ^ (1 - ε) * d) :=
      mul_le_mul h2 h1 hden.le (by linarith)
    have h4 : 4 * Q * (1200 * (k : ℝ) ^ 4 * d ^ (1 - ε) * d) =
        (19200 * (k : ℝ) ^ 4 * Q) * (d ^ (1 - ε) * d) / 4 := by ring
    have h5 : (19200 * (k : ℝ) ^ 4 * Q) * (d ^ (1 - ε) * d) ≤ d ^ (3 * ε / 4) * (d ^ (1 - ε) * d) :=
      mul_le_mul_of_nonneg_right hfe (mul_nonneg hdε.le R.d_pos.le)
    have h6 : (E / 2) ^ 2 = d ^ (3 * ε / 4) * (d ^ (1 - ε) * d) / 4 := by
      rw [div_pow, hsq]; ring
    rw [h6]
    linarith
  -- `T · 2n ≤ 2 exp(2Q)`
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hTn : (T : ℝ) ≤ n := by exact_mod_cast hT
  have hT2 : (T : ℝ) * (2 * n) ≤ 2 * Real.exp (2 * Q) := by
    have : (T : ℝ) * (2 * n) ≤ 2 * (Real.exp Q * Real.exp Q) := by
      have h1 : (T : ℝ) * n ≤ Real.exp Q * Real.exp Q :=
        mul_le_mul (hTn.trans hn) hn hn0 (Real.exp_pos _).le
      linarith
    rw [← Real.exp_add, ← two_mul] at this
    exact this
  have hexp : Real.exp (-((E / 2) ^ 2 /
      (2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (E / 2 + 5 * k * d)))) ≤
      Real.exp (-(2 * Q + 2)) := Real.exp_le_exp.mpr (by linarith)
  have he2 : 4 ≤ Real.exp 2 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hfin : 2 * Real.exp (2 * Q) * Real.exp (-(2 * Q + 2)) = 2 / Real.exp 2 := by
    rw [mul_assoc, ← Real.exp_add, show 2 * Q + -(2 * Q + 2) = -2 by ring, Real.exp_neg]
    ring
  calc (T : ℝ) * (2 * n) * Real.exp (-((E / 2) ^ 2 /
        (2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (E / 2 + 5 * k * d))))
      ≤ 2 * Real.exp (2 * Q) * Real.exp (-(2 * Q + 2)) :=
        mul_le_mul hT2 hexp (Real.exp_pos _).le (by positivity)
    _ = 2 / Real.exp 2 := hfin
    _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
        linarith
end GJKKL.Main.Regime
