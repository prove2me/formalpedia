-- Prove2me | solution 1 for GJKKL.Main.Regime.mu_le_eta4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:16.830218+00:00
-- url     : https://prove2.me/submissions/7a4765ca-a644-40d5-9dbb-3c8dead42775

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_P2M_GJKKL_Main_Regime___le_one_1ecfd2c91c46
public import Theorems.Thm_GJKKL_Main_Regime_rp_le

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : d ^ (-(ε ^ 3)) ≤ d ^ (-(ε ^ 4)) := by
  apply R.rp_le
  have h3 : 0 ≤ ε ^ 3 := pow_nonneg R.ε_pos.le 3
  have : ε ^ 4 ≤ ε ^ 3 := by
    calc ε ^ 4 = ε ^ 3 * ε := by ring
      _ ≤ ε ^ 3 * 1 := mul_le_mul_of_nonneg_left R.ε_le_one h3
      _ = ε ^ 3 := by ring
  linarith
end GJKKL.Main.Regime
