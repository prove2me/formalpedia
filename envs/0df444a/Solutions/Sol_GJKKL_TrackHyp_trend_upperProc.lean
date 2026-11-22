-- Prove2me | solution 1 for GJKKL.TrackHyp.trend_upperProc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:48.914405+00:00
-- url     : https://prove2.me/submissions/45e243af-7240-4b79-9979-f395c4c4dd1a

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_K1_nonneg
public import Theorems.Thm_GJKKL_TrackHyp_avail_bounds
public import Theorems.Thm_GJKKL_TrackHyp_sum_le_zero_of_mul
public import Theorems.Thm_GJKKL_TrackHyp_dv_bounds
public import Theorems.Thm_GJKKL_TrackHyp_dv_le_card_avail
public import Theorems.Thm_GJKKL_TrackHyp_card_sdiff_Dv
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_Trajectory_trend_upper
public import Theorems.Thm_GJKKL_frozen_cons_of_covered
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_lossSum_ge_real
public import Theorems.Thm_GJKKL_sum_K_mul_increment
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
theorem _root_.solution {h : List (Finset V)} (hT : h.length < T) (hg : GoodState H dh δ h)
    (v : V) :
    ∑ a, (greedyKernel H).K h a * (upperProc H dh δ v (a :: h) - upperProc H dh δ v h) ≤ 0 := by
  by_cases hv : v ∈ covered h
  · refine le_of_eq (sum_eq_zero fun a _ => ?_)
    simp only [upperProc, frozen_cons_of_covered H _ a hv, sub_self, mul_zero]
  have hA := hyp.avail_bounds hg.1 hg.2.1
  have hApos : (0 : ℝ) < (avail H h).card := by
    exact_mod_cast card_pos.mpr hg.2.2
  refine hyp.sum_le_zero_of_mul hApos ?_
  have key := sum_K_mul_increment H hv 1 (fun t => -dh t - δ t)
  simp only [upperProc] at key ⊢
  rw [key, hyp.card_sdiff_Dv h v]
  have hD := hyp.dv_bounds hg.2.1 hv
  have := Trajectory.trend_upper (K1 := (k : ℝ) - 1)
    (κ := ((((k - 1) + (k - 1) * (k - 2) : ℕ) : ℝ))) (c := (c : ℝ)) (B := B)
    (dh := dh h.length) (δ := δ h.length) (aP := aPar V k h.length)
    (Asz := (avail H h).card) (D := dv H h v) (loss := lossSum H h v)
    (g := dh h.length - dh (h.length + 1)) (r := δ (h.length + 1) - δ h.length)
    hyp.K1_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (hyp.dh_pos _ hT)
    (hyp.δ_nonneg _ hT) (hyp.δ_le _ hT) (hyp.aP_ge _ hT) hD.1 hD.2 hA.1 hA.2
    (hyp.dv_le_card_avail h v) (lossSum_ge_real H hyp.unif hg.2.1 v hyp.codeg)
    (hyp.g_nonneg _ hT) (hyp.g_le _ hT) (hyp.r_ge _ hT) hyp.B_ge (hyp.B_c _ hT)
  have e : -1 * (lossSum H h v : ℝ) + ((avail H h).card - dv H h v) *
      ((-dh (h.length + 1) - δ (h.length + 1)) - (-dh h.length - δ h.length)) =
      -(lossSum H h v : ℝ) + ((avail H h).card - dv H h v) *
        ((dh h.length - dh (h.length + 1)) - (δ (h.length + 1) - δ h.length)) := by ring
  linarith [this, e]
end GJKKL.TrackHyp
