-- Prove2me | solution 1 for GJKKL.TrackHyp.freedman_lowerProc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:29.099794+00:00
-- url     : https://prove2.me/submissions/ee222ede-744f-4adf-8741-37f2b4d34190

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_r_nonneg
public import Theorems.Thm_GJKKL_TrackHyp_trend_lowerProc
public import Theorems.Thm_GJKKL_TrackHyp_inc_lowerProc
public import Theorems.Thm_GJKKL_TrackHyp_accSum_le
public import Theorems.Thm_GJKKL_History_freedman_super


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
theorem _root_.solution (v : V) {i : ℕ} (hi : i ≤ T) :
    prob (greedyKernel H) i (fun h => lam ≤ lowerProc H dh δ v h - lowerProc H dh δ v [] ∧
      AliveBefore (GoodState H dh δ) h) ≤ Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by
  have hφ : ∀ t < T, |(dh (t + 1) - δ (t + 1)) - (dh t - δ t)| ≤
      (dh t - dh (t + 1)) + (δ (t + 1) - δ t) := by
    intro t ht
    have := hyp.g_nonneg t ht; have := hyp.r_nonneg ht
    rw [abs_le]; constructor <;> linarith
  refine freedman_super (greedyKernel H) (lowerProc H dh δ v) (GoodState H dh δ) i C s lam
    hyp.C_pos hyp.s_pos hyp.lam_pos (fun h hT _ hg => ?_) (fun h hT _ hg a ha => ?_)
    (fun h hT hal hg => ?_)
  · exact hyp.trend_lowerProc (by omega) hg v
  · exact hyp.inc_lowerProc (by omega) v ha
  · have := hyp.accSum_le v (-1) (by norm_num) (fun t => dh t - δ t) hφ h (by omega) hal hg
    exact this.trans (hyp.s_ge _ (by omega))
end GJKKL.TrackHyp
