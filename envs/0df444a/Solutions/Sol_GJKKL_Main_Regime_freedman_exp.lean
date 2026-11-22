-- Prove2me | solution 1 for GJKKL.Main.Regime.freedman_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:09.31044+00:00
-- url     : https://prove2.me/submissions/b3ea9fdf-91e6-4b58-8e13-6e2b84377f48

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_cube_le
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
theorem _root_.solution : 19200 * (k : ℝ) ^ 4 * d ^ (ε ^ 3) ≤ d ^ (3 * ε / 4) := by
  calc 19200 * (k : ℝ) ^ 4 * d ^ (ε ^ 3) ≤ d ^ (ε / 2) * d ^ (ε ^ 3) :=
        mul_le_mul_of_nonneg_right R.h2 (R.rp_pos _).le
    _ = d ^ (ε / 2 + ε ^ 3) := R.rp_mul _ _
    _ ≤ d ^ (3 * ε / 4) := R.rp_le (by linarith [R.cube_le, R.ε_pos])
end GJKKL.Main.Regime
