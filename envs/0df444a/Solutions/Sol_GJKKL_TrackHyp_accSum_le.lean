-- Prove2me | solution 1 for GJKKL.TrackHyp.accSum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:11.602741+00:00
-- url     : https://prove2.me/submissions/02c604ef-4f78-4fa9-8f4d-a641efc0b065

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_condAbsInc_le
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
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
open GJKKL.TrackHyp
variable {H : Finset (Finset V)} {k c : ℕ} {dh δ : ℕ → ℝ} {T : ℕ} {B lam C s : ℝ}
  (hyp : TrackHyp H k c dh δ T B lam C s)
include hyp
namespace GJKKL.TrackHyp
theorem _root_.solution (v : V) (σ : ℝ) (hσ : |σ| = 1) (φ : ℕ → ℝ)
    (hφ : ∀ t < T, |φ (t + 1) - φ t| ≤ (dh t - dh (t + 1)) + (δ (t + 1) - δ t)) :
    ∀ h : List (Finset V), h.length < T → AliveBefore (GoodState H dh δ) h →
      GoodState H dh δ h →
      accSum (greedyKernel H) (frozen H (fun t x => σ * x + φ t) v) h ≤
        ∑ t ∈ range (h.length + 1), bnd V k dh δ t
  | [], hT, _, hg => by
    simp only [accSum, List.length_nil, zero_add, sum_range_one]
    exact hyp.condAbsInc_le hT hg v σ hσ φ (hφ 0 hT)
  | a :: h, hT, hal, hg => by
    have hT' : h.length < T := by simp at hT; omega
    have ih := solution v σ hσ φ hφ h hT' hal.1 hal.2
    simp only [accSum, List.length_cons]
    rw [sum_range_succ]
    have := hyp.condAbsInc_le hT hg v σ hσ φ (hφ _ hT)
    simp only [List.length_cons] at this
    linarith
end GJKKL.TrackHyp
