-- Prove2me | solution 1 for GJKKL.Main.Regime.cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:51.320352+00:00
-- url     : https://prove2.me/submissions/d1834c06-6629-47b5-9ebf-0fb20abadd80

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_cube_bound

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : ε ^ 3 ≤ ε / 16 := by
  have hk := R.k_ge
  have h1 : (1 : ℝ) ≤ 32 * (k : ℝ) ^ 2 + k := by nlinarith
  have h3 : 0 ≤ ε ^ 3 := pow_nonneg R.ε_pos.le 3
  calc ε ^ 3 = ε ^ 3 * 1 := by ring
    _ ≤ ε ^ 3 * (32 * (k : ℝ) ^ 2 + k) := mul_le_mul_of_nonneg_left h1 h3
    _ ≤ ε / 16 := R.cube_bound
end GJKKL.Main.Regime
