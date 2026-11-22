-- Prove2me | solution 1 for GJKKL.Main.Regime.k_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:45.246025+00:00
-- url     : https://prove2.me/submissions/2cd324cc-aba9-4724-9c7a-ad28121cbc55

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [R.k_ge]
end GJKKL.Main.Regime
