-- Prove2me | solution 1 for GJKKL.TrackHyp.condAbsInc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:43.689125+00:00
-- url     : https://prove2.me/submissions/0174500c-fe26-4bdb-a613-610838230513

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_bnd_def
public import Theorems.Thm_GJKKL_TrackHyp_aP_pos
public import Theorems.Thm_GJKKL_TrackHyp_K1_nonneg
public import Theorems.Thm_GJKKL_TrackHyp_avail_bounds
public import Theorems.Thm_GJKKL_TrackHyp_dv_bounds
public import Theorems.Thm_GJKKL_TrackHyp_bnd_nonneg
public import Theorems.Thm_GJKKL_frozen_cons_of_covered
public import Theorems.Thm_GJKKL_lossSum_le_real
public import Theorems.Thm_GJKKL_sum_K_mul_abs_increment_le


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
    (v : V) (σ : ℝ) (hσ : |σ| = 1) (φ : ℕ → ℝ)
    (hφ : |φ (h.length + 1) - φ h.length| ≤
      (dh h.length - dh (h.length + 1)) + (δ (h.length + 1) - δ h.length)) :
    condAbsInc (greedyKernel H) (frozen H (fun t x => σ * x + φ t) v) h ≤
      bnd V k dh δ h.length := by
  unfold condAbsInc
  by_cases hv : v ∈ covered h
  · rw [sum_eq_zero fun a _ => by rw [frozen_cons_of_covered H _ a hv, sub_self, abs_zero,
      mul_zero]]
    exact hyp.bnd_nonneg hT
  have hA := hyp.avail_bounds hg.1 hg.2.1
  have hApos : (0 : ℝ) < (avail H h).card := by exact_mod_cast card_pos.mpr hg.2.2
  have key := sum_K_mul_abs_increment_le H hv σ hσ φ
  set S := ∑ a, (greedyKernel H).K h a *
    |frozen H (fun t x => σ * x + φ t) v (a :: h) - frozen H (fun t x => σ * x + φ t) v h|
  have hL : 0 < dh h.length - δ h.length := by
    linarith [hyp.δ_le _ hT, hyp.dh_pos _ hT]
  have hD := hyp.dv_bounds hg.2.1 hv
  have hloss := lossSum_le_real H hyp.unif hg.2.1 v hyp.codeg
  -- `S ≤ lossSum/|A| + |Δφ|`
  have h1 : S ≤ (lossSum H h v : ℝ) / (avail H h).card + |φ (h.length + 1) - φ h.length| := by
    rw [div_add' _ _ _ hApos.ne', le_div_iff₀ hApos]
    linarith
  have h2 : (lossSum H h v : ℝ) / (avail H h).card ≤
      ((k : ℝ) - 1) * (dh h.length + δ h.length) ^ 2 /
        (aPar V k h.length * (dh h.length - δ h.length)) := by
    have hP := mul_pos (hyp.aP_pos hT) hL
    rw [div_le_div_iff₀ hApos hP]
    have hU : 0 ≤ dh h.length + δ h.length := by linarith
    calc (lossSum H h v : ℝ) * (aPar V k h.length * (dh h.length - δ h.length))
        ≤ ((dh h.length + δ h.length) * ((k : ℝ) - 1) * (dh h.length + δ h.length)) *
            (aPar V k h.length * (dh h.length - δ h.length)) := by
          apply mul_le_mul_of_nonneg_right _ hP.le
          refine hloss.trans ?_
          apply mul_le_mul_of_nonneg_right _ hU
          exact mul_le_mul_of_nonneg_right hD.2 hyp.K1_nonneg
      _ ≤ ((k : ℝ) - 1) * (dh h.length + δ h.length) ^ 2 * (avail H h).card := by
          have : ((dh h.length + δ h.length) * ((k : ℝ) - 1) * (dh h.length + δ h.length)) *
              (aPar V k h.length * (dh h.length - δ h.length)) =
              ((k : ℝ) - 1) * (dh h.length + δ h.length) ^ 2 *
                (aPar V k h.length * (dh h.length - δ h.length)) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hA.1 (mul_nonneg hyp.K1_nonneg (sq_nonneg _))
  rw [bnd_def]
  linarith
end GJKKL.TrackHyp
