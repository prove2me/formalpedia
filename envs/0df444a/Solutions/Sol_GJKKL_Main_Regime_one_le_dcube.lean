-- Prove2me | solution 1 for GJKKL.Main.Regime.one_le_dcube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:33.207832+00:00
-- url     : https://prove2.me/submissions/1dc5d957-1416-4b9f-9c6c-fca1a9bb0a29

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
theorem _root_.solution : 1 ≤ d ^ (ε ^ 3) := one_le_rpow R.one_le_d (pow_nonneg R.ε_pos.le 3)
end GJKKL.Main.Regime
