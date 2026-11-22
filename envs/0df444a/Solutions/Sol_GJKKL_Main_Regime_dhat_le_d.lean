-- Prove2me | solution 1 for GJKKL.Main.Regime.dhat_le_d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:22.966083+00:00
-- url     : https://prove2.me/submissions/cf9e03b9-c7d2-426c-91aa-a383e35e585b

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
theorem _root_.solution {a : ℝ} {t : ℕ} (hx0 : 0 ≤ pfrac a t) (hx1 : pfrac a t ≤ 1) :
    dhat k d a t ≤ d := by
  unfold dhat
  have : pfrac a t ^ (k - 1) ≤ 1 := pow_le_one₀ hx0 hx1
  nlinarith [R.d_pos]
end GJKKL.Main.Regime
