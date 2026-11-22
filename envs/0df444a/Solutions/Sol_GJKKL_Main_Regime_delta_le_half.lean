-- Prove2me | solution 1 for GJKKL.Main.Regime.delta_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:14.486982+00:00
-- url     : https://prove2.me/submissions/d566d6a7-9526-45c1-8918-2f8455bf6f99

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_GJKKL_Main_Regime_mu_le_one
public import Theorems.Thm_GJKKL_Main_Regime_delta_le_dhat

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
    delta k ε d a t ≤ dhat k d a t / 2 := by
  have h := R.delta_le_dhat hμx hx1
  have hd : 0 ≤ dhat k d a t := by
    unfold dhat; exact mul_nonneg R.d_pos.le (pow_nonneg (R.mu_pos.trans_le hμx).le _)
  have := R.mu_le_one
  nlinarith
end GJKKL.Main.Regime
