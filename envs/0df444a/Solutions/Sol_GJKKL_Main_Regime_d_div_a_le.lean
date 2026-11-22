-- Prove2me | solution 1 for GJKKL.Main.Regime.d_div_a_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:46.963736+00:00
-- url     : https://prove2.me/submissions/88922caa-ff36-4d62-be74-b13491d7ceef

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_k_pos
public import Theorems.Thm_GJKKL_Main_Regime_rp_pos
public import Theorems.Thm_GJKKL_Main_Regime_d_split
public import Theorems.Thm_GJKKL_Main_Regime_n_pos
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
theorem _root_.solution : d / (n / k) ≤ 2 * k * d ^ (1 - ε) := by
  have hk := R.k_ge
  have hnp := R.n_pos hn
  have ha : 0 < n / k := div_pos hnp R.k_pos
  rw [div_le_iff₀ ha]
  have h1 : d ^ ε / 2 ≤ n := by
    have : d ^ ε / 2 ≤ ((k : ℝ) - 1) * d ^ ε / 2 := by
      have := (R.rp_pos ε).le; nlinarith
    linarith
  have h2 : d ^ (1 - ε) * (d ^ ε / 2) ≤ d ^ (1 - ε) * n :=
    mul_le_mul_of_nonneg_left h1 (R.rp_pos _).le
  have h3 : d ^ (1 - ε) * (d ^ ε / 2) = d / 2 := by
    calc d ^ (1 - ε) * (d ^ ε / 2) = (d ^ (1 - ε) * d ^ ε) / 2 := by ring
      _ = d / 2 := by rw [R.d_split]
  have h4 : 2 * k * d ^ (1 - ε) * (n / k) = 2 * (d ^ (1 - ε) * n) := by
    calc 2 * k * d ^ (1 - ε) * (n / k) = 2 * (d ^ (1 - ε) * n) * (k / k) := by ring
      _ = 2 * (d ^ (1 - ε) * n) := by rw [div_self R.k_pos.ne', mul_one]
  rw [h4]
  linarith
end GJKKL.Main.Regime
