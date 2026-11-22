-- Prove2me | solution 1 for GJKKL.Main.Regime.mu_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:11.90363+00:00
-- url     : https://prove2.me/submissions/379876de-179b-4f93-b36a-1c73eac628ba

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
theorem _root_.solution : d ^ (-(ε ^ 3)) < 1 :=
  rpow_lt_one_of_one_lt_of_neg (by linarith [R.d_ge]) (by have := pow_pos R.ε_pos 3; linarith)
end GJKKL.Main.Regime
