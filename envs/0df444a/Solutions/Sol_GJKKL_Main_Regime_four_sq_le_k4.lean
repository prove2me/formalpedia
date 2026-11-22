-- Prove2me | solution 1 for GJKKL.Main.Regime.four_sq_le_k4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:41.074973+00:00
-- url     : https://prove2.me/submissions/71b2ece9-9a5a-400e-85d9-c37d583166ac

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : 4 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
  have h1 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [R.k_ge]
  have := mul_le_mul_of_nonneg_right h1 (sq_nonneg (k : ℝ))
  nlinarith
end GJKKL.Main.Regime
