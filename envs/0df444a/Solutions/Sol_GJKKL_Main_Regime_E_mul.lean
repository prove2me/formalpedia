-- Prove2me | solution 1 for GJKKL.Main.Regime.E_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:20.156137+00:00
-- url     : https://prove2.me/submissions/ab1ee199-04c8-476d-88e5-2cf01b60dcbb

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_cube_le
public import Theorems.Thm_GJKKL_Main_Regime_rp_le
public import Theorems.Thm_GJKKL_Main_Regime_rp_mul

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : d * d ^ (ε / 2) ≤ d ^ (1 - ε / 8) * d ^ (ε - ε ^ 3) := by
  calc d * d ^ (ε / 2) = d ^ (1 : ℝ) * d ^ (ε / 2) := by rw [rpow_one]
    _ = d ^ (1 + ε / 2) := R.rp_mul _ _
    _ ≤ d ^ (1 - ε / 8 + (ε - ε ^ 3)) := R.rp_le (by linarith [R.cube_le, R.ε_pos])
    _ = d ^ (1 - ε / 8) * d ^ (ε - ε ^ 3) := (R.rp_mul _ _).symm
end GJKKL.Main.Regime
