-- Prove2me | solution 1 for GJKKL.Main.Regime.mu_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:57.997872+00:00
-- url     : https://prove2.me/submissions/47b7d407-1e8a-4053-835a-5228bb2c399d

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
theorem _root_.solution (n : ℕ) : (d ^ (-(ε ^ 3))) ^ n = d ^ (-(ε ^ 3) * n) := by
  rw [rpow_mul R.d_pos.le, rpow_natCast]
end GJKKL.Main.Regime
