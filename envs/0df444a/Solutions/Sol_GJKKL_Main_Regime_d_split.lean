-- Prove2me | solution 1 for GJKKL.Main.Regime.d_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:56.044706+00:00
-- url     : https://prove2.me/submissions/c1e72228-748b-4939-a2b5-042d0a79b0d6

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
theorem _root_.solution : d ^ (1 - ε) * d ^ ε = d := by
  rw [R.rp_mul, sub_add_cancel, rpow_one]
end GJKKL.Main.Regime
