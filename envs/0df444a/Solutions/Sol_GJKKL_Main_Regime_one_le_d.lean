-- Prove2me | solution 1 for GJKKL.Main.Regime.one_le_d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:02.638856+00:00
-- url     : https://prove2.me/submissions/da9acb5b-f0b3-4198-ad15-5f064f8e27f0

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : 1 ≤ d := by linarith [R.d_ge]
end GJKKL.Main.Regime
