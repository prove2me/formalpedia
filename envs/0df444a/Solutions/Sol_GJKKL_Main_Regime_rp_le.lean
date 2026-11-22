-- Prove2me | solution 1 for GJKKL.Main.Regime.rp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:32.883668+00:00
-- url     : https://prove2.me/submissions/00a04df2-4f98-4351-809a-e1104e77375f

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
theorem _root_.solution {x y : ℝ} (h : x ≤ y) : d ^ x ≤ d ^ y := rpow_le_rpow_of_exponent_le R.one_le_d h
end GJKKL.Main.Regime
