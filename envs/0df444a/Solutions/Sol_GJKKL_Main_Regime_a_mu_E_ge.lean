-- Prove2me | solution 1 for GJKKL.Main.Regime.a_mu_E_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:50.999662+00:00
-- url     : https://prove2.me/submissions/90339dba-5583-4522-9154-a605bd285daa

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_k_pos
public import Theorems.Thm_GJKKL_Main_Regime_k_le_sq
public import Theorems.Thm_GJKKL_Main_Regime_sq_le_k4
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_GJKKL_Main_Regime_E_pos
public import Theorems.Thm_P2M_GJKKL_Main_Regime_d__mu_c9b4f7c228e3
public import Theorems.Thm_GJKKL_Main_Regime_E_mul
public import Theorems.Thm_GJKKL_TrackHyp_k_pos


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {n : ℝ} (hn : ((k : ℝ) - 1) * d ^ ε / 2 ≤ n)
include hn
namespace GJKKL.Main.Regime
theorem _root_.solution : d ≤ n / k * d ^ (-(ε ^ 3)) * d ^ (1 - ε / 8) := by
  have hk := R.k_ge
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ R.k_pos]
  have hE := R.E_pos
  have h3 : ((k : ℝ) - 1) * d ^ ε / 2 * d ^ (-(ε ^ 3)) * d ^ (1 - ε / 8) ≤
      n * d ^ (-(ε ^ 3)) * d ^ (1 - ε / 8) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn R.mu_pos.le) hE.le
  have h4 : ((k : ℝ) - 1) * d ^ ε / 2 * d ^ (-(ε ^ 3)) * d ^ (1 - ε / 8) =
      ((k : ℝ) - 1) / 2 * (d ^ (1 - ε / 8) * d ^ (ε - ε ^ 3)) := by
    rw [← R.dε_mu]; ring
  have h5 : d * d ^ (ε / 2) ≤ d ^ (1 - ε / 8) * d ^ (ε - ε ^ 3) := R.E_mul
  have h6 : d * (19200 * (k : ℝ) ^ 4) ≤ d * d ^ (ε / 2) :=
    mul_le_mul_of_nonneg_left R.h2 R.d_pos.le
  have h7 : 1 / 2 * (d * (19200 * (k : ℝ) ^ 4)) ≤
      ((k : ℝ) - 1) / 2 * (d ^ (1 - ε / 8) * d ^ (ε - ε ^ 3)) :=
    mul_le_mul (by linarith) (h6.trans h5) (mul_nonneg R.d_pos.le (by positivity)) (by linarith)
  have h8 : d * k ≤ 1 / 2 * (d * (19200 * (k : ℝ) ^ 4)) := by
    have : (k : ℝ) ≤ 9600 * (k : ℝ) ^ 4 := by linarith [R.k_le_sq, R.sq_le_k4]
    nlinarith [R.d_pos]
  linarith
end GJKKL.Main.Regime
