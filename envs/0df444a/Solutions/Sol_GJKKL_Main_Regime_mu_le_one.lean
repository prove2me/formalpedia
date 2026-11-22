-- Prove2me | solution 1 for GJKKL.Main.Regime.mu_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:12.4037+00:00
-- url     : https://prove2.me/submissions/1a7d7c0f-0b3d-478c-bfa6-e94be7ef7f9e

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_one_le_d

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : d ^ (-(ε ^ 3)) ≤ 1 :=
  rpow_le_one_of_one_le_of_nonpos R.one_le_d (by have := pow_pos R.ε_pos 3; linarith)
end GJKKL.Main.Regime
