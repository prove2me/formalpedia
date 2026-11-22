-- Prove2me | solution 1 for GJKKL.Main.Regime.half_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:15.355494+00:00
-- url     : https://prove2.me/submissions/111b3ca5-2746-4d12-aca5-15016bcbefca

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_cube_le
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
theorem _root_.solution : d ^ (ε / 2) ≤ d ^ (ε - ε ^ 3) :=
  R.rp_le (by linarith [R.cube_le, R.ε_pos])
end GJKKL.Main.Regime
