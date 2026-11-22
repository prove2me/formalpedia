-- Prove2me | solution 1 for GJKKL.Main.Regime.n_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:36.817038+00:00
-- url     : https://prove2.me/submissions/04f5535c-8391-46f6-bf78-19427731c787

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_P2M_GJKKL_Main_Regime_d__ge_two_14571f3b3df4

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {n : ℝ} (hn : ((k : ℝ) - 1) * d ^ ε / 2 ≤ n)
include hn
namespace GJKKL.Main.Regime
theorem _root_.solution : 0 < n := by
  have := R.k_ge; have := R.dε_ge_two
  nlinarith
end GJKKL.Main.Regime
