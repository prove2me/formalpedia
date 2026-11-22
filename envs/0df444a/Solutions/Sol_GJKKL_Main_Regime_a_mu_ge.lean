-- Prove2me | solution 1 for GJKKL.Main.Regime.a_mu_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:57.68855+00:00
-- url     : https://prove2.me/submissions/89560937-68a7-43f7-ac2c-d4bdc5f070e3

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_k_pos
public import Theorems.Thm_GJKKL_Main_Regime_sq_le_k4
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_P2M_GJKKL_Main_Regime_d__mu_c9b4f7c228e3
public import Theorems.Thm_GJKKL_Main_Regime_half_le
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
theorem _root_.solution : 16 * (k : ℝ) ≤ n / k * d ^ (-(ε ^ 3)) := by
  have hk := R.k_ge
  rw [div_mul_eq_mul_div, le_div_iff₀ R.k_pos]
  have h3 : ((k : ℝ) - 1) * d ^ ε / 2 * d ^ (-(ε ^ 3)) ≤ n * d ^ (-(ε ^ 3)) :=
    mul_le_mul_of_nonneg_right hn R.mu_pos.le
  have h4 : ((k : ℝ) - 1) * d ^ ε / 2 * d ^ (-(ε ^ 3)) = ((k : ℝ) - 1) / 2 * d ^ (ε - ε ^ 3) := by
    rw [← R.dε_mu]; ring
  have h2 : 19200 * (k : ℝ) ^ 4 ≤ d ^ (ε - ε ^ 3) := R.h2.trans R.half_le
  have h5 : 1 / 2 * (19200 * (k : ℝ) ^ 4) ≤ ((k : ℝ) - 1) / 2 * d ^ (ε - ε ^ 3) :=
    mul_le_mul (by linarith) h2 (by positivity) (by linarith)
  have h6 : 16 * (k : ℝ) * k ≤ 1 / 2 * (19200 * (k : ℝ) ^ 4) := by
    have := R.sq_le_k4
    nlinarith
  linarith
end GJKKL.Main.Regime
