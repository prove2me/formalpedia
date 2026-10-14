-- Prove2me | solution 1 for DbarRegularity.dbar_sobolev_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T15:31:51.522718+00:00
-- url     : https://prove2.me/submissions/16844989-c2ac-4a5f-a2f0-13e72ec953e7

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_eLpNorm_iteratedFDeriv_succ_le_dbar
import Theorems.Thm_DbarRegularity_eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_euclidean
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic



namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem dbar_sobolev_estimate_aux (n k : ℕ) (p R : ℝ) (hk : 1 ≤ k) (hp : 1 < p) (hR : 0 < R) :
    ∃ M : ℝ≥0, ∀ (c : ℂ) (φ : ℂ → EuclideanSpace ℂ (Fin n)), ContDiff ℝ ∞ φ →
      tsupport φ ⊆ ball c R →
      sobolevNorm k (ENNReal.ofReal p) (ball c R) φ
        ≤ M * sobolevNorm (k - 1) (ENNReal.ofReal p) (ball c R) (dbar φ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨A, hA⟩ := cauchyRiemann_lp_euclidean n p hp
  obtain ⟨B, hB⟩ := eLpNorm_iteratedFDeriv_succ_le_dbar n p hp
  refine ⟨(2 * R).toNNReal * A + ∑ i ∈ Finset.range (m + 1), 2 ^ i * B,
    fun c φ hφ hsupp => ?_⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (mod_cast le_top)
  have hcs : HasCompactSupport φ :=
    (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport φ)
      (hsupp.trans ball_subset_closedBall)
  set q := ENNReal.ofReal p
  -- the right-hand side is the whole-plane norm
  have htd : tsupport (dbar φ) ⊆ ball c R := by
    refine (closure_mono ?_).trans ((tsupport_fderiv_subset ℝ (f := φ)).trans hsupp)
    intro z hz
    by_contra h0
    apply hz
    have : fderiv ℝ φ z = 0 := by simpa using h0
    simp [dbar, this]
  set T : ℕ → ℝ≥0∞ := fun i => eLpNorm (iteratedFDeriv ℝ i (dbar φ)) q volume with hT
  set S := ∑ i ∈ Finset.range (m + 1), T i with hS
  have hRHS : sobolevNorm (m + 1 - 1) q (ball c R) (dbar φ) = S := by
    rw [Nat.add_sub_cancel]
    unfold sobolevNorm
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsub : Function.support (iteratedFDeriv ℝ i (dbar φ)) ⊆ ball c R :=
      (support_iteratedFDeriv_subset i).trans htd
    have hsub' : Function.support (fun z => ‖iteratedFDeriv ℝ i (dbar φ) z‖) ⊆ ball c R :=
      fun z hz => hsub (Function.mem_support.2 (norm_ne_zero_iff.1 (Function.mem_support.1 hz)))
    calc eLpNorm (iteratedFDeriv ℝ i (dbar φ)) q (volume.restrict (ball c R))
        = eLpNorm (fun z => ‖iteratedFDeriv ℝ i (dbar φ) z‖) q (volume.restrict (ball c R)) :=
          (eLpNorm_norm _).symm
      _ = eLpNorm (fun z => ‖iteratedFDeriv ℝ i (dbar φ) z‖) q volume :=
          eLpNorm_restrict_eq_of_support_subset hsub'
      _ = T i := eLpNorm_norm _
  have hTS : ∀ i ∈ Finset.range (m + 1), T i ≤ S := fun i hi =>
    Finset.single_le_sum (f := T) (fun _ _ => bot_le) hi
  -- the left-hand side is at most the whole-plane norm
  have hLHS : sobolevNorm (m + 1) q (ball c R) φ
      ≤ ∑ i ∈ Finset.range (m + 1), eLpNorm (iteratedFDeriv ℝ (i + 1) φ) q volume
        + eLpNorm φ q volume := by
    unfold sobolevNorm
    rw [Finset.sum_range_succ']
    refine add_le_add (Finset.sum_le_sum fun i _ =>
      eLpNorm_mono_measure _ Measure.restrict_le_self) ?_
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (le_of_eq ?_)
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun z => norm_iteratedFDeriv_zero)
  -- zeroth-order term
  have h0 : eLpNorm φ q volume ≤ ENNReal.ofReal (2 * R) * A * S := by
    have hP := eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center c R p hp.le φ hφ1
      hsupp
    have hCR := hA φ hφ1 hcs
    have hT0 : eLpNorm (dbar φ) q volume ≤ S := by
      have := hTS 0 (by simp)
      refine le_trans (le_of_eq ?_) this
      exact (eLpNorm_congr_norm_ae
        (Eventually.of_forall fun z => norm_iteratedFDeriv_zero)).symm
    calc eLpNorm φ q volume
        ≤ ENNReal.ofReal (2 * R) * eLpNorm (fun z => fderiv ℝ φ z 1) q volume := hP
      _ ≤ ENNReal.ofReal (2 * R) * (eLpNorm (fun z => fderiv ℝ φ z 1) q volume
            + eLpNorm (fun z => fderiv ℝ φ z Complex.I) q volume) := by gcongr; exact le_self_add
      _ ≤ ENNReal.ofReal (2 * R) * (A * eLpNorm (dbar φ) q volume) := by gcongr
      _ ≤ ENNReal.ofReal (2 * R) * (A * S) := by gcongr
      _ = ENNReal.ofReal (2 * R) * A * S := by ring
  -- higher-order terms
  have h1 : ∑ i ∈ Finset.range (m + 1), eLpNorm (iteratedFDeriv ℝ (i + 1) φ) q volume
      ≤ (∑ i ∈ Finset.range (m + 1), ((2 ^ i * B : ℝ≥0) : ℝ≥0∞)) * S := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    exact (hB i φ hφ hcs).trans (by gcongr; exact hTS i hi)
  rw [hRHS]
  refine hLHS.trans ((add_le_add h1 h0).trans (le_of_eq ?_))
  have hc : ((2 * R).toNNReal : ℝ≥0∞) = ENNReal.ofReal (2 * R) := rfl
  push_cast
  rw [hc]
  ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution (n k : ℕ) (p R : ℝ) (hk : 1 ≤ k) (hp : 1 < p) (hR : 0 < R) :
    ∃ M : ℝ≥0, ∀ (c : ℂ) (φ : ℂ → EuclideanSpace ℂ (Fin n)), ContDiff ℝ ∞ φ →
      tsupport φ ⊆ ball c R →
      sobolevNorm k (ENNReal.ofReal p) (ball c R) φ
        ≤ M * sobolevNorm (k - 1) (ENNReal.ofReal p) (ball c R) (dbar φ) :=
  dbar_sobolev_estimate_aux n k p R hk hp hR
