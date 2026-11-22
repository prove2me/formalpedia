-- Prove2me | solution 1 for GJKKL.Main.Regime.rp_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:11.026307+00:00
-- url     : https://prove2.me/submissions/bb6b7b27-7d7b-4bfb-afc7-be842ed74ada

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_d_pos

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution (x : ℝ) : 0 < d ^ x := rpow_pos_of_pos R.d_pos x
end GJKKL.Main.Regime
