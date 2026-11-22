-- Prove2me | solution 1 for GJKKL.Main.Regime.key_E
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:22.993336+00:00
-- url     : https://prove2.me/submissions/085271de-1dc0-4d70-a13d-cefc8a85d9af

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_cube_bound
public import Theorems.Thm_GJKKL_Main_Regime_rp_le
public import Theorems.Thm_GJKKL_Main_Regime_rp_mul
public import Theorems.Thm_GJKKL_Main_Regime_rp_pos
public import Theorems.Thm_GJKKL_Main_Regime_mu_pow
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution : 2 * d ^ (1 - ε / 8) ≤ d * (d ^ (-(ε ^ 3))) ^ (Bn k + k) := by
  have hcb := R.cube_bound
  rw [R.mu_pow]
  calc 2 * d ^ (1 - ε / 8) ≤ d ^ (ε / 16) * d ^ (1 - ε / 8) :=
        mul_le_mul_of_nonneg_right R.h16 (R.rp_pos _).le
    _ = d ^ (ε / 16 + (1 - ε / 8)) := R.rp_mul _ _
    _ ≤ d ^ (1 + -(ε ^ 3) * ((Bn k + k : ℕ) : ℝ)) := by
        apply R.rp_le
        simp only [Bn]
        push_cast
        linarith
    _ = d * d ^ (-(ε ^ 3) * ((Bn k + k : ℕ) : ℝ)) := by
        rw [← R.rp_mul, rpow_one]
end GJKKL.Main.Regime
