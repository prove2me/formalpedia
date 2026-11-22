-- Prove2me | solution 1 for GJKKL.TrackHyp.inc_upperProc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:41.541913+00:00
-- url     : https://prove2.me/submissions/4068bf85-6dd5-43e3-856e-1c9ecda9823a

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_r_nonneg
public import Theorems.Thm_GJKKL_TrackHyp_mem_avail_of_K_ne
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_increment_abs_le
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
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
open GJKKL.TrackHyp
variable {H : Finset (Finset V)} {k c : ℕ} {dh δ : ℕ → ℝ} {T : ℕ} {B lam C s : ℝ}
  (hyp : TrackHyp H k c dh δ T B lam C s)
include hyp
namespace GJKKL.TrackHyp
theorem _root_.solution {h : List (Finset V)} (hT : h.length < T) (v : V) {a : Finset V}
    (ha : (greedyKernel H).K h a ≠ 0) :
    |upperProc H dh δ v (a :: h) - upperProc H dh δ v h| ≤ C := by
  have := increment_abs_le H hyp.unif hyp.codeg (v := v) (hyp.mem_avail_of_K_ne ha) 1
    (by norm_num) (fun t => -dh t - δ t)
  simp only [upperProc]
  refine this.trans ?_
  have hg := hyp.g_nonneg _ hT
  have hr := hyp.r_nonneg hT
  have habs : |(-dh (h.length + 1) - δ (h.length + 1)) - (-dh h.length - δ h.length)| ≤
      (dh h.length - dh (h.length + 1)) + (δ (h.length + 1) - δ h.length) := by
    rw [abs_le]; constructor <;> linarith
  linarith [hyp.C_ge _ hT]
end GJKKL.TrackHyp
