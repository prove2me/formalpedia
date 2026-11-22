-- Prove2me | solution 1 for GJKKL.Main.Regime.init_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:07.452795+00:00
-- url     : https://prove2.me/submissions/93b5e1e3-f2d2-4c52-88e5-7338beb1e3c4

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_rp_le
public import Theorems.Thm_GJKKL_Main_Regime_rp_mul
public import Theorems.Thm_GJKKL_Main_Regime_rp_pos

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : 2 * d ^ (1 - ε) ≤ d ^ (1 - ε / 8) := by
  calc 2 * d ^ (1 - ε) ≤ d ^ (ε / 16) * d ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right R.h16 (R.rp_pos _).le
    _ = d ^ (ε / 16 + (1 - ε)) := R.rp_mul _ _
    _ ≤ d ^ (1 - ε / 8) := R.rp_le (by linarith [R.ε_pos])
end GJKKL.Main.Regime
