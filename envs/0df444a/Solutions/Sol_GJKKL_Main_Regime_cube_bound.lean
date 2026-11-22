-- Prove2me | solution 1 for GJKKL.Main.Regime.cube_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:23.496448+00:00
-- url     : https://prove2.me/submissions/6568776a-80e1-45e6-add2-005cea231fa6

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_k_le_sq
public import Theorems.Thm_GJKKL_Main_Regime_four_sq_le_k4

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : ε ^ 3 * (32 * (k : ℝ) ^ 2 + k) ≤ ε / 16 := by
  have hk := R.k_ge
  have h0 : 0 ≤ ε * (64 * (k : ℝ) ^ 2) := mul_nonneg R.ε_pos.le (by positivity)
  have h1 : (ε * (64 * (k : ℝ) ^ 2)) ^ 2 ≤ 1 := by nlinarith [R.ε_small]
  have h2 : 32 * (k : ℝ) ^ 2 + k ≤ 256 * (k : ℝ) ^ 4 := by
    linarith [R.k_le_sq, R.four_sq_le_k4]
  have h3 : ε ^ 2 * (32 * (k : ℝ) ^ 2 + k) ≤ 1 / 16 := by
    calc ε ^ 2 * (32 * (k : ℝ) ^ 2 + k) ≤ ε ^ 2 * (256 * (k : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (ε * (64 * (k : ℝ) ^ 2)) ^ 2 / 16 := by ring
      _ ≤ 1 / 16 := by linarith
  calc ε ^ 3 * (32 * (k : ℝ) ^ 2 + k) = ε * (ε ^ 2 * (32 * (k : ℝ) ^ 2 + k)) := by ring
    _ ≤ ε * (1 / 16) := mul_le_mul_of_nonneg_left h3 R.ε_pos.le
    _ = ε / 16 := by ring
end GJKKL.Main.Regime
