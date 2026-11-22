-- Prove2me | solution 1 for GJKKL.Main.Regime.k_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:41:22.674809+00:00
-- url     : https://prove2.me/submissions/5aec6618-d7af-456b-90f7-ea34ff8cd357

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
theorem _root_.solution : (2 : ℝ) ≤ k := by exact_mod_cast R.two_le
end GJKKL.Main.Regime
