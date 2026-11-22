-- Prove2me | solution 1 for GJKKL.Main.Regime.delta_le_dhat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:22.937191+00:00
-- url     : https://prove2.me/submissions/bc4e1b37-53d2-4df4-8687-1bebd6cb4cac

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_GJKKL_Main_Regime_two_E_le

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution {a : ℝ} {t : ℕ} (hμx : d ^ (-(ε ^ 3)) ≤ pfrac a t) (hx1 : pfrac a t ≤ 1) :
    delta k ε d a t ≤ d ^ (-(ε ^ 3)) / 2 * dhat k d a t := by
  have hx : 0 < pfrac a t := R.mu_pos.trans_le hμx
  unfold delta dhat
  rw [div_le_iff₀ (pow_pos hx _)]
  have h := R.two_E_le hμx hx1
  rw [pow_add] at h
  nlinarith [R.mu_pos]
end GJKKL.Main.Regime
