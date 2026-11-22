-- Prove2me | solution 1 for GJKKL.Main.Regime.E_le_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:58.890405+00:00
-- url     : https://prove2.me/submissions/0c93d52a-64da-43b0-97ab-2586094b44d5

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_E_pos

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution {a : ℝ} {t : ℕ} (hx0 : 0 < pfrac a t) (hx1 : pfrac a t ≤ 1) :
    d ^ (1 - ε / 8) ≤ delta k ε d a t := by
  unfold delta
  rw [le_div_iff₀ (pow_pos hx0 _)]
  have : pfrac a t ^ Bn k ≤ 1 := pow_le_one₀ hx0.le hx1
  nlinarith [R.E_pos]
end GJKKL.Main.Regime
