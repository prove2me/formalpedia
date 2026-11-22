-- Prove2me | solution 1 for GJKKL.Main.Regime.dneg_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:45.405346+00:00
-- url     : https://prove2.me/submissions/f2d0da7a-cda1-4e87-a01d-e8f108f5daaf

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
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
theorem _root_.solution : d ^ (-ε) * d = d ^ (1 - ε) := by
  calc d ^ (-ε) * d = d ^ (-ε) * d ^ (1 : ℝ) := by rw [rpow_one]
    _ = d ^ (1 - ε) := by rw [R.rp_mul]; congr 1; ring
end GJKKL.Main.Regime
