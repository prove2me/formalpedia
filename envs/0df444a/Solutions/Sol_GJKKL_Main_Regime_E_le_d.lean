-- Prove2me | solution 1 for GJKKL.Main.Regime.E_le_d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:51.214731+00:00
-- url     : https://prove2.me/submissions/dfca52ba-d9e9-4ba9-a305-dde844a16749

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_rp_le

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : d ^ (1 - ε / 8) ≤ d := by
  calc d ^ (1 - ε / 8) ≤ d ^ (1 : ℝ) := R.rp_le (by linarith [R.ε_pos])
    _ = d := rpow_one d
end GJKKL.Main.Regime
